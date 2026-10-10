import OAI.Analysis.Cotype.CubeNoise
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.NoncommRing

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def projectionProduct : {n : ℕ} → (Fin n → X →L[ℝ] X) → X →L[ℝ] X
  | 0, _ => 1
  | _+1, P => P 0 * projectionProduct (fun i => P i.succ)

def projectionSubset {n : ℕ} (P : Fin n → X →L[ℝ] X) (ε : Cube n) : X →L[ℝ] X :=
  projectionProduct (fun i => if ε i then P i else 1)

theorem projectionProduct_commute {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (Q : X →L[ℝ] X) (h : ∀ i, Commute (P i) Q) :
    Commute (projectionProduct P) Q := by
  induction n with
  | zero => exact Commute.one_left Q
  | succ n ih => exact (h 0).mul_left (ih _ (fun i => h i.succ))

theorem projectionSubset_commute {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (ε : Cube n) (Q : X →L[ℝ] X) (h : ∀ i, Commute (P i) Q) :
    Commute (projectionSubset P ε) Q := by
  apply projectionProduct_commute
  intro i
  cases ε i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact Commute.one_left Q
  · exact h i

theorem projectionProduct_norm_apply {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (h : ∀ i x, ‖P i x‖ ≤ ‖x‖) (x : X) : ‖projectionProduct P x‖ ≤ ‖x‖ := by
  induction n with
  | zero => simp [projectionProduct]
  | succ n ih => exact (h 0 _).trans (ih _ (fun i => h i.succ))

theorem projectionSubset_norm_apply {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (h : ∀ i x, ‖P i x‖ ≤ ‖x‖) (ε : Cube n) (x : X) :
    ‖projectionSubset P ε x‖ ≤ ‖x‖ := by
  apply projectionProduct_norm_apply
  intro i z
  cases ε i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · simp
  · exact h i z

theorem projectionSubset_union {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (ε η : Cube n) :
    projectionSubset P ε * projectionSubset P η =
      projectionSubset P (fun i => ε i || η i) := by
  induction n with
  | zero => simp [projectionSubset, projectionProduct]
  | succ n ih =>
    have ht := ih (fun i => P i.succ) (fun i => hp i.succ)
      (fun i j => hc i.succ j.succ) (fun i => ε i.succ) (fun i => η i.succ)
    have hm := projectionSubset_commute (fun i => P i.succ) (fun i => ε i.succ)
      (P 0) (fun i => hc i.succ 0)
    change ((if ε 0 then P 0 else 1) * projectionSubset (fun i => P i.succ) (fun i => ε i.succ)) *
      ((if η 0 then P 0 else 1) * projectionSubset (fun i => P i.succ) (fun i => η i.succ)) =
      (if ε 0 || η 0 then P 0 else 1) *
        projectionSubset (fun i => P i.succ) (fun i => ε i.succ || η i.succ)
    cases he : ε 0 <;> cases hh : η 0 <;> simp only [Bool.false_or, Bool.true_or,
      Bool.false_eq_true, ite_false, ite_true, one_mul]
    · exact ht
    · rw [← mul_assoc, hm.eq, mul_assoc, ht]
    · rw [mul_assoc, ht]
    · rw [mul_assoc, ← mul_assoc (projectionSubset _ _) (P 0), hm.eq,
        mul_assoc, ← mul_assoc (P 0) (P 0), hp, ht]

theorem projectionProduct_one (n : ℕ) :
    projectionProduct (fun _ : Fin n => (1 : X →L[ℝ] X)) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [projectionProduct, ih]

theorem projectionSubset_singleton {n : ℕ} (P : Fin n → X →L[ℝ] X) (i : Fin n) :
    projectionSubset P (fun j => decide (j = i)) = P i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [projectionSubset, projectionProduct, projectionProduct_one]
    · have hi0 : (0 : Fin (n+1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)
      simpa [projectionSubset, projectionProduct, hi0] using
        ih (fun j => P j.succ) i

theorem projectionComplement_expansion {n : ℕ} (P : Fin n → X →L[ℝ] X) :
    projectionProduct (fun i => 1 - P i) =
      ∑ ε : Cube n, (∏ i, sign (ε i)) • projectionSubset P ε := by
  induction n with
  | zero => simp [projectionProduct, projectionSubset]
  | succ n ih =>
    rw [← (cubeCons n).sum_comp]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    change (1-P 0) * projectionProduct (fun i => 1-P i.succ) = _
    rw [ih]
    simp only [cubeCons, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      sign_false, sign_true, projectionSubset, projectionProduct, Bool.false_eq_true, ite_false, ite_true,
      one_mul, neg_one_mul, neg_smul]
    simp only [sub_mul, one_mul, Finset.mul_sum, mul_smul_comm]
    simp only [sub_eq_add_neg, smul_add, smul_neg,
      Finset.sum_add_distrib, Finset.sum_neg_distrib]
    abel

end Cotype

end

end OAI
