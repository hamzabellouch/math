import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanTransducer

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

def quote : List Bool → List Bool
  | [] => [false]
  | b::bs => true::b::quote bs

@[simp] theorem quote_length (bs : List Bool) : (quote bs).length=2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [quote,List.length_cons,ih]; omega

def encodePair {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (x : α × β) : List Bool :=
  quote (ea x.1)++eb x.2

@[simp] theorem encodePair_length {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (x : α × β) :
    (encodePair ea eb x).length=2*(ea x.1).length+1+(eb x.2).length := by
  simp only [encodePair,List.length_append,quote_length]

namespace WordTransducer

def quoting : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[true,b])
  finish _ := [false]

 theorem quoting_run (xs : List Bool) : quoting.run () xs=quote xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [Transducer.run,quoting,List.cons_append,List.nil_append,quote] using congrArg (fun l => true::b::l) ih

def projecting (tail : Bool) : Transducer where
  Q := Option Bool
  initial := none
  next q b := match q with
    | none => (some (!b),[])
    | some false => (none,if tail then [] else [b])
    | some true => (some true,if tail then [b] else [])
  finish _ := []

 theorem projecting_done (tail : Bool) (xs : List Bool) :
    (projecting tail).run (some true) xs=if tail then xs else [] := by
  induction xs with
  | nil => cases tail <;> rfl
  | cons b xs ih =>
      change (if tail then [b] else [])++(projecting tail).run (some true) xs=_
      rw [ih]
      cases tail <;> simp

 theorem projecting_pair (tail : Bool) (xs ys : List Bool) :
    (projecting tail).run none (quote xs++ys)=if tail then ys else xs := by
  induction xs with
  | nil => exact projecting_done tail ys
  | cons b xs ih =>
      change (if tail then [] else [b])++(projecting tail).run none (quote xs++ys)=_
      rw [ih]
      cases tail <;> simp

end WordTransducer

namespace PolyProgram

 def of_word {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    {g : List Bool → List Bool} (P : PolyProgram id id g)
    (h : ∀ a, g (ea a)=eb (f a)) : PolyProgram ea eb f where
  machine := P.machine
  time := P.time
  outputs a := by simpa only [id_eq,h a] using P.outputs (ea a)

 noncomputable def quote : PolyProgram id id Binary.quote :=
  WordTransducer.quoting.program.congr _ WordTransducer.quoting_run

 noncomputable def fst {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) ea Prod.fst :=
  (WordTransducer.projecting false).program.of_word (fun _ => by
    simpa only [encodePair,Bool.false_eq_true,ite_false,WordTransducer.projecting] using WordTransducer.projecting_pair false _ _)

 noncomputable def snd {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) eb Prod.snd :=
  (WordTransducer.projecting true).program.of_word (fun _ => by
    simpa only [encodePair,ite_true,WordTransducer.projecting] using WordTransducer.projecting_pair true _ _)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
