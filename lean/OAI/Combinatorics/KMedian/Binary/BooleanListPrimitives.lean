import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanEncoding
import OAI.Combinatorics.KMedian.Binary.BooleanLoop
import OAI.Combinatorics.KMedian.Binary.BooleanProducts

namespace OAI


                                             
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

def encodeBool (b : Bool) : List Bool := [b]

namespace WordTransducer

def emptyTest : Transducer where
  Q := Bool
  initial := true
  next _ _ := (false,[])
  finish b := [b]

 theorem emptyTest_run (q : Bool) (xs : List Bool) :
    emptyTest.run q xs=[q && xs.isEmpty] := by
  induction xs generalizing q with
  | nil => cases q <;> rfl
  | cons b xs ih =>
      change emptyTest.run false xs=_
      rw [ih]
      simp

def head : Transducer where
  Q := Option Bool
  initial := none
  next q b := (q.or (some b),[])
  finish q := [q.getD false]

 theorem head_run (q : Option Bool) (xs : List Bool) :
    head.run q xs=[(q.or xs.head?).getD false] := by
  induction xs generalizing q with
  | nil => cases q <;> rfl
  | cons b xs ih =>
      change head.run (q.or (some b)) xs=_
      rw [ih]
      cases q <;> rfl

def tail : Transducer where
  Q := Bool
  initial := true
  next q b := (false,if q then [] else [b])
  finish _ := []

 theorem tail_run_false (xs : List Bool) : tail.run false xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::tail.run false xs=b::xs; rw [ih]

 theorem tail_run (xs : List Bool) : tail.run true xs=xs.tail := by
  cases xs with
  | nil => rfl
  | cons b xs => exact tail_run_false xs

abbrev prepend : Transducer where
  Q := Fin 4
  initial := 0
  next q b := if q=0 then (1,[]) else if q=1 then (2,[b]) else if q=2 then (3,[]) else (3,[b])
  finish _ := []

 theorem prepend_done (xs : List Bool) : prepend.run 3 xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change b::prepend.run 3 xs=b::xs
      rw [ih]

 theorem prepend_run (b : Bool) (xs : List Bool) :
    prepend.run 0 (quote [b]++xs)=b::xs := by
  change b::prepend.run 3 xs=b::xs
  rw [prepend_done]

def prependWord (p : List Bool) : Transducer where
  Q := Bool
  initial := true
  next q b := (false,if q then p++[b] else [b])
  finish q := if q then p else []

 theorem prefix_done (p xs : List Bool) : (prependWord p).run false xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::(prependWord p).run false xs=b::xs; rw [ih]

 theorem prefix_run (p xs : List Bool) : (prependWord p).run true xs=p++xs := by
  cases xs with
  | nil => exact (List.append_nil p).symm
  | cons b xs =>
      change (p++[b])++(prependWord p).run false xs=p++b::xs
      rw [prefix_done,List.append_assoc,List.singleton_append]

def select : Transducer where
  Q := Fin 2 ⊕ (Bool × Option (Option Bool))
  initial := .inl 0
  next q b := match q with
    | .inl k => if k=0 then (.inl 1,[]) else (.inr (b,none),[])
    | .inr (keep,none) => (.inr (keep,some none),[])
    | .inr (keep,some none) => (.inr (keep,some (some (!b))),[])
    | .inr (keep,some (some false)) => (.inr (keep,some none),if keep then [] else [b])
    | .inr (keep,some (some true)) => (.inr (keep,some (some true)),if keep then [b] else [])
  finish _ := []

 theorem select_done (keep : Bool) (xs : List Bool) :
    select.run (.inr (keep,some (some true))) xs=if keep then xs else [] := by
  induction xs with
  | nil => cases keep <;> rfl
  | cons b xs ih =>
      change (if keep then [b] else [])++select.run (.inr (keep,some (some true))) xs=_
      rw [ih]
      cases keep <;> simp

 theorem select_pair (keep : Bool) (xs ys : List Bool) :
    select.run (.inr (keep,some none)) (quote xs++ys)=if keep then ys else xs := by
  induction xs with
  | nil => exact select_done keep ys
  | cons b xs ih =>
      change (if keep then [] else [b])++select.run (.inr (keep,some none)) (quote xs++ys)=_
      rw [ih]
      cases keep <;> simp

 theorem select_run (keep : Bool) (xs ys : List Bool) :
    select.run (.inl 0) (quote [keep]++quote xs++ys)=if keep then ys else xs := by
  exact select_pair keep xs ys

end WordTransducer

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

noncomputable def isEmpty : PolyProgram id encodeBool List.isEmpty :=
  WordTransducer.emptyTest.program.of_word (fun xs => by
    simpa only [WordTransducer.emptyTest,Bool.true_and,encodeBool,id_eq] using WordTransducer.emptyTest_run true xs)

noncomputable def head : PolyProgram id encodeBool (fun xs => xs.head?.getD false) :=
  WordTransducer.head.program.of_word (fun xs => by
    simpa only [WordTransducer.head,Option.or,encodeBool,id_eq] using WordTransducer.head_run none xs)

noncomputable def tail : PolyProgram id id List.tail :=
  WordTransducer.tail.program.of_word (fun xs => by
    simpa only [WordTransducer.tail,id_eq] using WordTransducer.tail_run xs)

noncomputable def cons : PolyProgram (encodePair encodeBool id) id (fun x => x.1::x.2) :=
  WordTransducer.prepend.program.of_word (fun x => by
    simpa only [WordTransducer.prepend,encodePair,encodeBool,id_eq] using WordTransducer.prepend_run x.1 x.2)

noncomputable def prependWord (p : List Bool) : PolyProgram id id (fun xs => p++xs) :=
  (WordTransducer.prependWord p).program.of_word (fun xs => by
    simpa only [WordTransducer.prependWord,id_eq] using WordTransducer.prefix_run p xs)

noncomputable def injectLeft (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram eb (encodeLoop ea eb) Sum.inl :=
  (prependWord [false]).of_word (fun _ => rfl)

noncomputable def injectRight (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram ea (encodeLoop ea eb) Sum.inr :=
  (prependWord [true]).of_word (fun _ => rfl)

noncomputable def select (eb : β → List Bool) :
    PolyProgram (encodePair encodeBool (encodePair eb eb)) eb
      (fun x => if x.1 then x.2.2 else x.2.1) :=
  WordTransducer.select.program.of_word (fun x => by
    simpa only [WordTransducer.select,encodePair,encodeBool,List.append_assoc,apply_ite] using
      WordTransducer.select_run x.1 (eb x.2.1) (eb x.2.2))

noncomputable def ite {p : α → Bool} {f g : α → β}
    (P : PolyProgram ea encodeBool p) (F : PolyProgram ea eb f) (G : PolyProgram ea eb g) :
    PolyProgram ea eb (fun a => if p a then g a else f a) :=
  ((P.fanout (F.fanout G)).comp (select eb)).congr _ (fun _ => rfl)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
