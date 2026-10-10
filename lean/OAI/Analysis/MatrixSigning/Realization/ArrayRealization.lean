import Mathlib
import OAI.Analysis.MatrixSigning.Realization.ScalarRealization
import OAI.Analysis.MatrixSigning.Realization.NaturalRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def natIsZero : Realizes natCode boolCode (fun n => decide (n=0)) where
  cost := fun n => n+6
  routine := by
    have h := WordOperations.isEmpty.reindex natCode
    refine { scratch := h.scratch,program := h.program,spec := ?_ }
    intro n
    simpa [natCode,boolCode,List.replicate_eq_nil_iff] using h.spec n

variable {α γ : Type*}
def lookupStep (p : (ℕ×α)×α) : ℕ×α :=
  if p.1.1=0 then p.1 else (p.1.1-1,if p.1.1-1=0 then p.2 else p.1.2)

def lookupStepRealizes (ea : α → Word) :
    Realizes (prodCode (prodCode natCode ea) ea) (prodCode natCode ea) lookupStep :=
  let old := first (prodCode natCode ea) ea
  let k := old.then (first natCode ea)
  let prev := old.then (second natCode ea)
  let x := second (prodCode natCode ea) ea
  let km := k.then natPred
  ((k.then natIsZero).ite old (km.both ((km.then natIsZero).ite x prev))).congr (by
    intro p
    simp [lookupStep,Nat.pred_eq_sub_one])

lemma lookupStep_zero (xs : List α) (a : α) :
    (xs.foldl (fun s x => lookupStep (s,x)) (0,a))=(0,a) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [lookupStep] using ih

lemma lookupStep_getD (xs : List α) (k : ℕ) (a : α) :
    (xs.foldl (fun s x => lookupStep (s,x)) (k+1,a)).2=xs.getD k a := by
  induction xs generalizing k a with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero =>
      rw [List.foldl_cons]
      change (xs.foldl (fun s x => lookupStep (s,x)) (0,x)).2=_
      rw [lookupStep_zero]
      simp
    | succ k => simpa [lookupStep,Nat.add_sub_cancel] using ih k a

def getD (ea : α → Word) (a : α) :
    Realizes (prodCode natCode (listCode ea)) ea (fun p => p.2.getD p.1 a) :=
  let k := first natCode (listCode ea)
  let xs := second natCode (listCode ea)
  let init := (k.then natSucc).both (constant (prodCode natCode (listCode ea)) ea a)
  (((init.both xs).then (lookupStepRealizes ea).fold).then (second natCode ea)).congr (by
    intro p
    exact lookupStep_getD p.2 p.1 a)

lemma fold_length (xs : List α) (n : ℕ) : xs.foldl (fun k _ => k+1) n=n+xs.length := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_comm,Nat.add_left_comm]

def lengthList (ea : α → Word) : Realizes (listCode ea) natCode List.length :=
  (((constant (listCode ea) natCode 0).both (identity (listCode ea))).then
    ((first natCode ea).then natSucc).fold).congr (by
      intro xs
      simp)

def Realizes.tabulate {ec : γ → Word} {ea : α → Word} {f : γ×ℕ → α}
    (r : Realizes (prodCode ec natCode) ea f) :
    Realizes (prodCode ec natCode) (listCode ea)
      (fun p => (List.range p.2).map (fun i => f (p.1,i))) :=
  ((first ec natCode).both ((second ec natCode).then range)).then r.mapCtx

lemma fold_natAdd (n k z : ℕ) : (fun a : ℕ×ℕ => (a.1,a.1+a.2))^[n] (k,z)=(k,n*k+z) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih];simp [Nat.add_mul,Nat.add_comm,Nat.add_left_comm]

def natMul : Realizes (prodCode natCode natCode) natCode (fun p => p.1*p.2) :=
  let l := first natCode natCode
  let r := second natCode natCode
  let init := r.both (constant (prodCode natCode natCode) natCode 0)
  let step := (first natCode natCode).both natAdd
  (((l.both init).then step.iterate).then (second natCode natCode)).congr (by
    intro p
    simp only [fold_natAdd,Nat.add_zero])

lemma iterate_ratSucc (n : ℕ) (q : ℚ) : (fun x : ℚ => x+1)^[n] q=q+n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih];push_cast;ring

def natToRat : Realizes natCode ratCode (fun n => (n : ℚ)) :=
  let step := (identity ratCode).add (constant ratCode ratCode 1)
  (((identity natCode).both (constant natCode ratCode 0)).then step.iterate).congr (by
    intro n
    simp only [iterate_ratSucc,zero_add,id_eq])

end CurrentKS.Realization

end

end OAI
