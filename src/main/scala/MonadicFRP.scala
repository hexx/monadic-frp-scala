// | Monadic FRP basic definitions and composition functions.
//   See the paper "Monadic Functional Reactive Programming" Atze van der Ploeg. Haskell Symposium '13<http://homepages.cwi.nl/~ploeg/papers/monfrp.pdf>. An example can be found at <https://github.com/cwi-swat/monadic-frp>.
//
//  Notice that currently Monadic FRP relies on a closed union (ADT) of basic events, which has the following downsides:
//    * Reactive level sharing requires an explicit call to a memoization function
//    * Reactive level recursion is problematic.
//
//
//  A function preprended with i indices a initialized signal variant of an signal computation function.

import scalaz._, Scalaz._

object MonadicFRP {
  // * Basic definitions

  sealed trait Event[A]
  case object Request extends Event[Nothing]
  case class Occurred[A](a: A) extends Event[A]

  // |An alias for a set of event requests
  type EvReqs[E] = Set[E]
  // |An alias for a set of event occurances
  type EvOccs[E] = Set[E]

  def singleton[E](e: E) = Set(e)
  def empty[E] = Set[E]()
  def undefined: Nothing = ???

  // | A reactive computation
  type React[E, A] = Done[A] \/ Await[E, A]
  case class Done[A](alpha: A)
  case class Await[E, A](reqs: EvReqs[E], f: EvOccs[E] => React[E, A])

  // | Request a single event
  def exper[E](a: E): React[E, E] = Await(singleton(a), (occs: EvOccs[E]) => Done(occs.toList.head).left).right

  // | The interpreter for reactive computations. The first argument
  // is a function that answers event requests in the monad m, the second
  // is the reactive computation.
  def interpret[M[_]: Monad, E, A](p: EvReqs[E] => M[EvOccs[E]], r: React[E, A]): M[A] = r match {
    case -\/(Done(a))     => Monad[M].point(a)
    case \/-(Await(e, c)) => p(e) >>= (occs => interpret(p, c(occs)))
  }

  // | A signal computation is a reactive computation of an initialized signal
  case class Sig[E, A, B](r: React[E, ISig[E, A, B]])

  // | An initialized signal
  type ISig[E, A, B] = End[B] \/ :|[E, A, B]
  case class End[B](b: B)
  case class :|[E, A, B](a: A, sig: Sig[E, A, B])

  // | The interpreter for signal computations taking three arguments:
  //
  //   * a function that answers event requests in the monad m
  //
  //   * a function that processes the emitted values in the monad m
  //
  //   * the signal computation.
  def interpretSig[M[_]: Monad, E, R, A, B](p: EvReqs[E] => M[EvOccs[E]], d: A => M[R], sig: Sig[E, A, B]): M[B] =
    interpret(p, sig.r) >>= (_ match {
      case -\/(End(a)) => Monad[M].point(a)
      case \/-(h :| t) => d(h) >> interpretSig(p, d, t)
    })

  implicit def reactMonad[E]: Monad[({type r[a] = React[E, a]})#r] = new Monad[({type r[a] = React[E, a]})#r] {
    def point[A](a: => A): React[E, A] = Done(a).left
    def bind[A, B](fa: React[E, A])(f: A => React[E, B]): React[E, B] = fa match {
      case -\/(Done(a))     => f(a)
      case \/-(Await(e, c)) => Await(e, (occs: EvOccs[E]) => c(occs) >>= f).right
    }
  }

  // | Run two reactive computations in parallel until either completes, and return the state of both.
  //    Notice that
  // @
  //     flip first == first
  //  @
  def first[E, A, B](l: React[E, A], r: React[E, B]): React[E, (React[E, A], React[E, B])] = (l, r) match {
    case (\/-(Await(el, _)), \/-(Await(er, _))) =>
      val c = (b: EvOccs[E]) => first(update(l, b), update(r, b))
      Await(el union er, c).right
    case _ => Done((l, r)).left
  }

  // | Alias for |first|
  def parR[E, A, B](l: React[E, A], r: React[E, B]): React[E, (React[E, A], React[E, B])] = first(l, r)

  // | Call the continuation function of a reactive computation if it awaits at least one of the event occurences.
  def update[E, A](r: React[E, A], b: EvOccs[E]): React[E, A] = r match {
    case \/-(Await(e, c)) if !filterOccs(b, e).isEmpty => c(filterOccs(b, e))
    case r => r
  }

  // | Filter those event occurences that anwer a request.
  def filterOccs[E](occs: EvOccs[E], reqs: EvReqs[E]): EvOccs[E] = occs intersect reqs

  // below: Section 4

  // Sequential composition
  implicit def sigFunctor[E, A]: Functor[({type s[b] = Sig[E, A, b]})#s] = new Functor[({type s[b] = Sig[E, A, b]})#s] {
    def map[B, C](fb: Sig[E, A, B])(f: B => C): Sig[E, A, C] =
      Sig(Functor[({type r[a] = React[E, a]})#r].map(fb.r)(isig => Functor[({type s[b] = ISig[E, A, b]})#s].map(isig)(f)))
  }

  implicit def sigMonad[E, A]: Monad[({type s[b] = Sig[E, A, b]})#s] = new Monad[({type s[b] = Sig[E, A, b]})#s] {
    def point[B](b: => B): Sig[E, A, B] = emitAll(End(b).left)
    def bind[B, C](fa: Sig[E, A, B])(f: B => Sig[E,A,C]): Sig[E,A,C] =
      Sig(fa.r >>= {
        case -\/(End(a)) => f(a).r
        case \/-(h :| t) => Monad[({type r[a] = React[E, a]})#r].point(:|(h, t >>= f).right)
      })
  }

  implicit def isigMonad[E, A]: Monad[({type s[b] = ISig[E, A, b]})#s] = new Monad[({type s[b] = ISig[E, A, b]})#s] {
    def point[B](b: => B): ISig[E, A, B] = End(b).left
    def bind[B, C](fa: ISig[E, A, B])(f: B => ISig[E, A, C]): ISig[E, A, C] = fa match {
      case -\/(End(b)) => f(b)
      case \/-(h :| t) => :|(h, t >>= ((b: B) => emitAll(f(b)))).right
    }
  }

  // * Repetition
  // | Repeat the given reactive computation indefinitely, each time emitting its result.
  def repeat[E, A, B](x: React[E, A]): Sig[E, A, B] = {
    def xs: Sig[E, A, B] = Sig(Functor[({type r[a] = React[E, a]})#r].map(x)(:|(_, xs).right))
    xs
  }

  // | Repeat the given signal computation indefinitely, each time emitting its initialized signal result.
  def spawn[E, A, B](sig: Sig[E, A, B]) = repeat(sig.r)

  // * Transformation
  // | Transform the emmited values of a signal computation by applying the function to each of them.
  def map[E, A, B, C](f: A => C, sig: Sig[E, A, B]): Sig[E, C, B] =
    Sig(Functor[({type r[a] = React[E, a]})#r].map(sig.r)(imap(f, _)))

  // | Transform the emmited values of an initialized signal computation by applying the function to each of them.
  def imap[E, A, B, C](f: A => C, isig: ISig[E, A, B]): ISig[E, C, B] = isig match {
    case -\/(End(b)) => -\/(End(b))
    case \/-(h :| t) => :|(f(h), map(f, t)).right
  }

  // | The list function scanl is similar to foldl, but returns a list of successive reduced values instead of a single value.
  // the signal variant works analogously.
  def scanl[E, A, B, C](f: (C, A) => C, i: C, sig: Sig[E, A, B]): Sig[E, C, B] = emitAll(iscanl(f, i, sig))

  def iscanl[E, A, B, C](f: (C, A) => C, i: C, sig: Sig[E, A, B]): ISig[E, C, B] = {
    :|(i, Monad[({type s[b] = Sig[E, C, b]})#s].bind(waitFor[E, C, ISig[E, A, B]](sig.r)) {
      case -\/(End(b)) => Monad[({type s[b] = Sig[E, C, b]})#s].point(b)
      case \/-(h :| t) => scanl(f, f(i, h), t)
    }).right
  }

  // | Run the signal computation as long as the given predicate does not hold on the emitted values. Once a value is emmited on which the predicate holds, the rest of the signal computation is returned.
  def break[E, A, B](f: A => Boolean, sig: Sig[E, A, B]): Sig[E, A, ISig[E, A, B]] =
    Sig(Functor[({type r[a] = React[E, a]})#r].map(sig.r)(ibreak(f, _)))

  def ibreak[E, A, B](f: A => Boolean, isig: ISig[E, A, B]): ISig[E, A, ISig[E, A, B]] = isig match {
    case \/-(h :| t) if !f(h) => :|(h, break(f, t)).right
    case _ => Monad[({type s[b] = ISig[E, A, b]})#s].point(isig)
  }

  // | |foldl| on signal computations behaves the same as waiting for the signal computation to end and then applying the 'fold' on the list of emitted values.
  def foldl[E, A, B, C](f: (A, B) => A, i: A, sig: Sig[E, B, C]): React[E, A] = sig.r >>= (ifoldl(f, i, _))

  def ifoldl[E, A, B, C](f: (A, B) => A, i: A, isig: ISig[E, B, C]): React[E, A] = isig match {
    case -\/(_)      => Monad[({type r[a] = React[E, a]})#r].point(i)
    case \/-(h :| t) => foldl(f, f(i, h), t)
  }

  // | Find the first emmited value on which the predicate hold.
  def find[E, A, B](f: A => Boolean, sig: Sig[E, A, B]): React[E, Option[A]] = Functor[({type r[a] = React[E, a]})#r].map(res(break(f, sig)))(icur)

  // * Parallel composition
  // | Sample the form of the signal computation at the time the reactive computation completes
  def at[E, A, B, C](sig: Sig[E, A, B], r: React[E, C]): React[E, Option[A]] =
    Functor[({type r[a] = React[E, a]})#r].map(res(until(sig, r)))(s => cur(s._1))

  // | Run the signal computation until the reactive computation completes, and return the new state of both computations.
  def until[E, A, B, C](sig: Sig[E, A, B], r: React[E, C]): Sig[E, A, (Sig[E, A, B], React[E, C])] = {
    val M = Monad[({type s[b] = Sig[E, A, b]})#s]
    def un(r2: (React[E, ISig[E, A, B]], React[E, C])): Sig[E, A, (Sig[E, A, B], React[E,C])] = r2 match {
      case (-\/(Done(l)), a) =>
        M.bind(emitAll(iuntil(l, a))){ case (l, a) => M.point(emitAll(l), a) }
      case (l, a) => M.point(Sig(l), a)
    }
    val r0: React[E, (React[E, ISig[E,A,B]], React[E, C])] = first(sig.r, r)
    M.bind(waitFor(r0))(un)
  }

  def iuntil[E, A, B, C](isig: ISig[E, A, B], r: React[E, C]): ISig[E, A, (ISig[E, A, B], React[E, C])] = isig match {
    case -\/(End(b)) =>
      val isig: ISig[E, A, B] = End(b).left
      End((isig, r)).left
    case \/-(h :| t) =>
      def cont(r2: (React[E, ISig[E, A, B]], React[E, C])): ISig[E, A, (ISig[E, A, B], React[E, C])] = r2 match {
        case (-\/(Done(l)), a) => iuntil(l, a)
        case (t, -\/(Done(a))) =>
          val i: ISig[E, A, B] = :|(h, Sig(t)).right
          val r: React[E, C] = Done(a).left
          End(i, r).left
        case _ => sys.error("iuntil cont")
      }
      :|(h, Sig(Functor[({type r[a] = React[E, a]})#r].map(first(t.r, r))(cont))).right
  }

  // | Apply the values from the second signal computation to the values from the first signal computation over time. When one ends, the new state of both is returned.
  def <^>[E, A, B, C, D](l: Sig[E, A => B, C], r: Sig[E, A, D]): Sig[E, B, (ISig[E, A => B, C], ISig[E, A, D])] = {
    val M = Monad[({type s[b] = Sig[E, B, b]})#s]
    M.bind(waitFor(bothStart(l, r))) {
      case (l, r) => emitAll(imap((f2: (A => B, A)) => f2._1(f2._2), pairs(l, r)))
    }
  }

  // | Wait for both signal computation to become initialized, and then return both their initizialized signals.
  def bothStart[E, A, B, C, D](l: Sig[E, A, B], r: Sig[E, C, D]): React[E, (ISig[E, A, B], ISig[E, C, D])] = {
    val M = Monad[({type r[a] = React[E, a]})#r]
    M.bind(res(until(l, r.r))) { case (Sig(l), r) =>
      M.bind(res(until(Sig(r), l))) { case (Sig(r), l) =>
        M.point((done0(l), done0(r)))
      }
    }
  }

  // | Emitted the pairs of the emitted values from both signal computations over time.  When one ends, the new state of both is returned.
  def pairs[E, A, B, C, D](isig1: ISig[E, A, B], isig2: ISig[E, C, D]): ISig[E, (A, C), (ISig[E, A, B], ISig[E, C, D])] = (isig1, isig2) match {
    case (-\/(End(a)), b) =>
      val isig0: (ISig[E, A, B], ISig[E, C, D]) = (End(a).left, b)
      End(isig0).left
    case (a, -\/(End(b))) =>
      val isig0: (ISig[E, A, B], ISig[E, C, D]) = (a, End(b).left)
      End(isig0).left
    case (\/-(hl :| Sig(tl)), \/-(hr :| Sig(tr))) =>
      def cont(r2: (React[E, ISig[E, A, B]], React[E, ISig[E, C, D]])): ISig[E, (A, C), (ISig[E, A, B], ISig[E, C, D])] =
        pairs(lup(hl, r2._1), lup(hr, r2._2))
      def lup[E, A, B](h: A, t: React[E, ISig[E, A, B]]): ISig[E, A, B] = t match {
        case -\/(Done(l)) => l
        case _            => :|(h, Sig(t)).right
      }
      val tail: Sig[E, (A, C), (ISig[E, A, B], ISig[E, C, D])] = Sig(Functor[({type r[a] = React[E, a]})#r].map(first(tl, tr))(cont))
      val head: (A, C) = (hl, hr)
      :|[E, (A, C), (ISig[E, A, B], ISig[E, C, D])](head, tail).right
  }

  // | Sample the former signal computation each time the later emits a value.
  def indexBy[E, A, B, C, D](l: Sig[E, A, B], r: Sig[E, C, D]): Sig[E, A, Unit] = {
    val M = Monad[({type s[b] = Sig[E, A, b]})#s]
    M.bind(waitFor(res(until(l, r.r)))) {
      case (Sig(_)           , -\/(Done(-\/(End(_))))) => M.point(())
      case (Sig(-\/(Done(l))), r                     ) => iindexBy(l, Sig(r))
      case (Sig(l)           , -\/(Done(\/-(_ :| r)))) => indexBy(Sig(l), r)
      case _                                           => sys.error("indexBy")
    }
  }

  def iindexBy[E, A, B, C, D](l: ISig[E, A, B], r: Sig[E, C, D]): Sig[E, A, Unit] = {
    val M = Monad[({type s[b] = Sig[E, A, b]})#s]
    M.bind(waitFor(ires(iuntil(l, r.r)))) {
      case (\/-(hl :| tl), -\/(Done(\/-(hr :| tr)))) =>
        val s: Sig[E, A, Unit] = emit(hl)
        val i: ISig[E, A, B] = :|(hl, tl).right
        s >> iindexBy(i,  tr)
      case _ => M.point(())
    }
  }

  // * Conversion
  // | Convert a initialized signal to a signal computation
  def emitAll[E, A, B](isig: ISig[E, A, B]): Sig[E, A, B] = Sig(Done(isig).left)

  // | Emit a single value in the signal computation mondad
  def emit[E, A](a: A): Sig[E, A, Unit] = emitAll(:|(a, Monad[({type s[b] = Sig[E, A, b]})#s].point(())).right)

  // | A signal that alway has the given form.
  def always[E, A, B](a: A): Sig[E, A, B] = {
    val M = Monad[({type s[b] = Sig[E, A, b]})#s]
    M.bind(emit(a))(_ => hold)
  }

  // | Convert a reactive computation to a signal computation.
  def waitFor[E, A, B](r: React[E, B]): Sig[E, A, B] = Sig(Functor[({type r[a] = React[E, a]})#r].map(r)(End(_).left))

  // | The reactive computation that never completes.
  def hold[E, A, B]: Sig[E, A, B] = {
    def never: React[E, B] = Await(empty, undefined).right
    waitFor(never)
  }

  // | Convert the result of a signal computation to a reactive computation.
  def res[E, A, B](sig: Sig[E, A, B]): React[E, B] = sig.r >>= ires

  // | Convert the result of an initialized signal a reactive computation.
  def ires[E, A, B](isig: ISig[E, A, B]): React[E, B] = isig match {
    case -\/(End(a)) => Done(a).left
    case \/-(h :| t) => res(t)
  }

  // implicit def reactFunctor[E]: Functor[({type r[a] = React[E, a]})#r] = new Functor[({type r[a] = React[E, a]})#r] {
  //   def map[A, B](fa: React[E, A])(f: A => B): React[E, B] = ???
  // }

  // | Return the result of a reactive computation if it is done
  def done[E, A](r: React[E, A]): Option[A] = r match {
    case -\/(Done(a)) => Option(a)
    case \/-(_)       => None
  }

  // | Give the current value of a signal computation, if any.
  def cur[E, A, B](sig: Sig[E, A, B]): Option[A] = sig match {
    case Sig(-\/(Done(\/-(h :| _)))) => Option(h)
    case _                           => None
  }

  // | the head of an initalized signal, if any.
  def icur[E, A, B](isig: ISig[E, A, B]): Option[A] = isig match {
    case -\/(_)      => None
    case \/-(h :| t) => Option(h)
  }

  // | Version of 'done' that throws an error if it the result is not done.
  def done0[E, A](r: React[E, A]): A = done(r).get

  // * Dynamic lists

  // | Cons the values from the first signal computation to the values form the latter signal computation over time.
  def cons[E, A, B, C](h: ISig[E, A, B], t: ISig[E, List[A], C]): ISig[E, List[A], Unit] = {
    val M = Monad[({type s[b] = ISig[E, List[A], b]})#s]
    M.bind(imap((ht: (A, List[A])) => ht._1 :: ht._2, pairs(h, t))) {
      case (h, t) => M.bind(imap((a: A) => List(a), h))(_ =>
        M.bind(t)(_ => M.point(()))
      )
    }
  }

  // | Run the initialized signals from the given signal computation in parallel, and emit the lists of the current form of all alive initialized signals.
  def parList[E, A, B, C](sig: Sig[E, ISig[E, A, B], C]): Sig[E, List[A], Unit] = emitAll(iparList(sig))

  def iparList[E, A, B, C](sig: Sig[E, ISig[E, A, B], C]): ISig[E, List[A], Unit] = {
    val M = Monad[({type s[b] = ISig[E, List[A], b]})#s]
    def rl[E, A, B, C](isig: ISig[E, List[A], Unit], sig: Sig[E, ISig[E, A, B], C]): ISig[E, List[A], Unit] = {
      val M = Monad[({type s[b] = ISig[E, List[A], b]})#s]
      M.bind(iuntil(isig, sig.r)) {
        case (t, -\/(Done(\/-(e :| es)))) => rl(cons(e, t), es)
        case (t, _                      ) => t
      }
    }
    val h: Sig[E, List[A], Unit] = hold[E, List[A], Unit]
    val l: List[A] = List()
    val i: ISig[E, List[A], Unit] = :|(l, h).right
    M.bind(rl(i, sig))(_ => M.point(()))
  }

  // * Memoization

  // | Memoize the continuation function of the reactive computation, and the continuation function of all next states.
  def memo[E, A](react: React[E, A]): React[E, A] = react match {
    case -\/(Done(_))     => react
    case \/-(Await(r, c)) => Await(r, memof((occs: EvOccs[E]) => memo(c(occs)))).right
  }

  // | Memoize the reactive computation of the initialized signal, and memoize the signal computation of the tail (if any).
  def memoSig[E, A, B](sig: Sig[E, A, B]): Sig[E, A, B] = {
    val M = Functor[({type r[a] = React[E, a]})#r]
    Sig(memo(M.map(sig.r)(imemoSig)))
  }

  def imemoSig[E, A, B](isig: ISig[E, A, B]): ISig[E, A, B] = isig match {
    case -\/(_)      => isig
    case \/-(h :| t) => :|(h, memoSig(t)).right
  }

  // Give a memoized version of the argument function. (not exported)
  def memof[A, B](f: A => B): A => B = {
    (x: A) => {
      var m = Map[A, B]()
      m.get(x) match {
        case None    =>
          val v = f(x)
          m += x -> v
          v
        case Some(v) => v
      }
    }
  }
}
