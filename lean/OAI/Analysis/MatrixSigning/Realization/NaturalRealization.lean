import Mathlib
import OAI.Analysis.MatrixSigning.Realization.IterateRoutine
import OAI.Analysis.MatrixSigning.Realization.ListRealization

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

abbrev natCode (k : ℕ) : Word := List.replicate k true

def natSucc : Realizes natCode natCode Nat.succ where
  cost := fun _ => 1
  routine := {
    scratch := 0
    program := KS.W20.Wire.push 0 true
    spec := fun k => by
      have h := KS.W20.Wire.push_spec (0 : Fin 1) true (io (natCode k))
      convert h using 1
      funext j;fin_cases j;simp [io,natCode,Function.update,List.replicate_succ] }

def natPred : Realizes natCode natCode Nat.pred where
  cost := fun _ => 1
  routine := {
    scratch := 0
    program := KS.W23.LiteralProgram.pop 0
    spec := fun k => by
      have h := KS.W23.LiteralProgram.pop_spec (0 : Fin 1) (io (natCode k))
      convert h using 1
      funext j;fin_cases j;cases k <;> simp [io,natCode,Function.update] }

def natAdd : Realizes (prodCode natCode natCode) natCode (fun p => p.1+p.2) where
  cost := fun p => 5*p.1+4
  routine := by
    have h := WordOperations.appending.reindex (fun p : ℕ×ℕ => (natCode p.1,natCode p.2))
    refine { scratch := h.scratch,program := h.program,spec := ?_ }
    intro p
    have hp := h.spec p
    simp only [natCode,List.length_replicate,List.replicate_add] at hp ⊢
    exact hp

variable {α : Type*} {ea : α → Word}
def Realizes.iterate {f : α → α} (r : Realizes ea ea f) :
    Realizes (prodCode natCode ea) ea (fun p => f^[p.1] p.2) where
  cost := fun p => 3*p.1+2+IterateRoutine.loopTicks r.cost f p.1 p.2
  routine := IterateRoutine.routine r.routine

def rangeStep (p : ℕ×List ℕ) : ℕ×List ℕ := (p.1+1,p.1::p.2)
def rangeStepRealizes : Realizes (prodCode natCode (listCode natCode))
    (prodCode natCode (listCode natCode)) rangeStep :=
  let idx := first natCode (listCode natCode)
  let acc := second natCode (listCode natCode)
  (idx.then natSucc).both ((idx.both acc).then (consList natCode))

lemma rangeStep_iterate (n : ℕ) : rangeStep^[n] (0,[])=(n,(List.range n).reverse) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    simp [rangeStep,List.range_succ]

def range : Realizes natCode (listCode natCode) List.range :=
  let init := constant natCode (prodCode natCode (listCode natCode)) (0,[])
  let run := ((identity natCode).both init).then rangeStepRealizes.iterate
  ((run.then (second natCode (listCode natCode))).then (reverseList natCode)).congr (by
    intro n
    simp only [rangeStep_iterate,List.reverse_reverse,id_eq])

end CurrentKS.Realization

end OAI
