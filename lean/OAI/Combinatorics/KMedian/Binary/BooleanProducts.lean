import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanEncoding
import OAI.Combinatorics.KMedian.Binary.BooleanParallelTransducer
import OAI.Combinatorics.KMedian.Binary.BooleanThread

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace WordTransducer

def identity : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[b])
  finish _ := []

 theorem identity_run (xs : List Bool) : identity.run () xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::identity.run () xs=b::xs; rw [ih]

def constant (s : List Bool) : Transducer where
  Q := Unit
  initial := ()
  next _ _ := ((),[])
  finish _ := s

 theorem constant_run (s xs : List Bool) : (constant s).run () xs=s := by
  induction xs with
  | nil => rfl
  | cons b xs ih => exact ih

def duplicate : ParallelTransducer where
  Q := Unit
  initial := ()
  next _ b := ((),([true,b],[b]))
  finish _ := ([false],[])

 theorem duplicate_run (xs : List Bool) : duplicate.run () xs=(quote xs,xs) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change (true::b::(duplicate.run () xs).1,b::(duplicate.run () xs).2)=_
      rw [ih]
      rfl

def exchange : ParallelTransducer where
  Q := Option Bool
  initial := none
  next q b := match q with
    | none => (some (!b),([],[]))
    | some false => (none,([],[b]))
    | some true => (some true,([true,b],[]))
  finish _ := ([false],[])

 theorem exchange_done (xs : List Bool) : exchange.run (some true) xs=(quote xs,[]) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change (true::b::(exchange.run (some true) xs).1,(exchange.run (some true) xs).2)=_
      rw [ih]
      rfl

 theorem exchange_run (xs ys : List Bool) : exchange.run none (quote xs++ys)=(quote ys,xs) := by
  induction xs with
  | nil => exact exchange_done ys
  | cons b xs ih =>
      change ((exchange.run none (quote xs++ys)).1,b::(exchange.run none (quote xs++ys)).2)=_
      rw [ih]

end WordTransducer

namespace PolyProgram
variable {α β γ δ : Type}
variable {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {ed : δ → List Bool}
variable {f : α → β} {g : γ → δ}

noncomputable def identity (ea : α → List Bool) : PolyProgram ea ea _root_.id :=
  WordTransducer.identity.program.of_word (fun a => by
    simpa only [WordTransducer.identity,id_eq] using WordTransducer.identity_run (ea a))

noncomputable def constant (ea : α → List Bool) (eb : β → List Bool) (b : β) :
    PolyProgram ea eb (fun _ => b) :=
  (WordTransducer.constant (eb b)).program.of_word (fun a => by
    simpa only [WordTransducer.constant] using WordTransducer.constant_run (eb b) (ea a))

noncomputable def duplicate (ea : α → List Bool) : PolyProgram ea (encodePair ea ea) (fun a => (a,a)) :=
  WordTransducer.duplicate.program.of_word (fun a => by
    have h := congrArg (fun p : List Bool × List Bool => p.1++p.2) (WordTransducer.duplicate_run (ea a))
    simpa only [WordTransducer.duplicate,encodePair] using h)

noncomputable def exchange (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) (encodePair eb ea) Prod.swap :=
  WordTransducer.exchange.program.of_word (fun x => by
    have h := congrArg (fun p : List Bool × List Bool => p.1++p.2) (WordTransducer.exchange_run (ea x.1) (eb x.2))
    simpa only [WordTransducer.exchange,encodePair,Prod.swap] using h)

noncomputable def second (P : PolyProgram ea eb f) (ec : γ → List Bool) :
    PolyProgram (encodePair ec ea) (encodePair ec eb) (fun x => (x.1,f x.2)) :=
  (((exchange ec ea).comp (P.thread ec)).comp (exchange eb ec)).congr _ (fun _ => rfl)

noncomputable def product (P : PolyProgram ea eb f) (Q : PolyProgram ec ed g) :
    PolyProgram (encodePair ea ec) (encodePair eb ed) (fun x => (f x.1,g x.2)) :=
  ((P.thread ec).comp (Q.second eb)).congr _ (fun _ => rfl)

noncomputable def fanout {h : α → γ} (P : PolyProgram ea eb f) (Q : PolyProgram ea ec h) :
    PolyProgram ea (encodePair eb ec) (fun a => (f a,h a)) :=
  ((duplicate ea).comp (P.product Q)).congr _ (fun _ => rfl)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
