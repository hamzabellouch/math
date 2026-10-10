import Mathlib
import OAI.Combinatorics.ThinTrees.Pencil.PointPrograms

namespace OAI

/-! Bool programs. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
variable {α : Type*} {ea : α → Word}

def Realizes.or {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (r : Realizes ea boolCode (fun a => decide (P a)))
    (s : Realizes ea boolCode (fun a => decide (Q a))) :
    Realizes ea boolCode (fun a => decide (P a ∨ Q a)) :=
  (r.ite (constant ea boolCode true) s).congr (by intro a;simp)
instance poly_or {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (r : Realizes ea boolCode (fun a => decide (P a)))
    (s : Realizes ea boolCode (fun a => decide (Q a))) [PolyTime r] [PolyTime s] : PolyTime (r.or s) := by
  unfold Realizes.or;infer_instance

abbrev boolsCode := listCode boolCode

def anyTrue : Realizes boolsCode boolCode (fun bs => decide (true ∈ bs)) :=
  ((constant boolsCode natCode 0).nlt
    ((((constant boolsCode boolCode false).both (identity boolsCode)).then
      (second boolCode boolCode).filterCtx).then (lengthList boolCode))).congr (by
      intro bs
      simp [List.length_pos_iff, List.filter_eq_nil_iff, Bool.forall_bool])
instance poly_anyTrue : PolyTime anyTrue := by unfold anyTrue;infer_instance

def allTrue : Realizes boolsCode boolCode (fun bs => decide (∀b∈bs,b=true)) :=
  (((identity boolCode).ite (constant boolCode boolCode false)
    (constant boolCode boolCode true)).map.then anyTrue).not.congr (by
      intro bs
      simp)
instance poly_allTrue : PolyTime allTrue := by unfold allTrue;infer_instance

variable {n : α → ℕ} {P : (a : α) → Fin (n a) → Prop} [∀a,DecidablePred (P a)]
def Realizes.existsFin
    (r : Realizes (finFamilyCode ea n) boolCode (fun p => decide (P p.1 p.2)))
    (rn : Realizes ea natCode n) : Realizes ea boolCode (fun a => decide (∃i,P a i)) :=
  ((r.tabulateFin rn).then anyTrue).congr (by
    intro a;simp only [List.mem_ofFn,decide_eq_true_eq])
instance poly_existsFin
    (r : Realizes (finFamilyCode ea n) boolCode (fun p => decide (P p.1 p.2)))
    (rn : Realizes ea natCode n) [PolyTime r] [PolyTime rn] : PolyTime (r.existsFin rn) := by
  unfold Realizes.existsFin;infer_instance

def Realizes.forallFin
    (r : Realizes (finFamilyCode ea n) boolCode (fun p => decide (P p.1 p.2)))
    (rn : Realizes ea natCode n) : Realizes ea boolCode (fun a => decide (∀i,P a i)) :=
  ((r.tabulateFin rn).then allTrue).congr (by
    intro a;simp only [List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,decide_eq_true_eq])
instance poly_forallFin
    (r : Realizes (finFamilyCode ea n) boolCode (fun p => decide (P p.1 p.2)))
    (rn : Realizes ea natCode n) [PolyTime r] [PolyTime rn] : PolyTime (r.forallFin rn) := by
  unfold Realizes.forallFin;infer_instance

lemma bools_length (bs : List Bool) : (boolsCode bs).length=3*bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change (listCode boolCode (b::bs)).length=_
    rw [listCode_cons,prodCode_length]
    change 2*1+1+(boolsCode bs).length=3*(bs.length+1)
    rw [ih];omega

lemma bools_ofFn_length {n : ℕ} (f : Fin n → Bool) :
    (boolsCode (List.ofFn f)).length=3*n := by rw [bools_length,List.length_ofFn]

end CurrentKS.Realization
end

end OAI
