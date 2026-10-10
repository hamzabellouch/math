import OAI.Analysis.Laughlin.Spin.Representation
import OAI.Analysis.Laughlin.Tensor.WeightProducts

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

theorem symmetricTensor_column_sum (Q : ℕ) (p : Fin (Q+1)) :
    (∑ a, symmetricTensorInclusion Q a p) = (Real.sqrt (Q.choose p.val : ℝ) : ℂ) := by
  have hr : (∑ a : Fin Q → Fin 2, symmetricTensorInclusionReal Q a p) =
      Real.sqrt (Q.choose p.val : ℝ) := by
    have hn : Real.sqrt (Q.choose p.val : ℝ) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (by exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ p.isLt))
    have he (a : Fin Q → Fin 2) : symmetricTensorInclusionReal Q a p =
        (Real.sqrt (Q.choose p.val : ℝ))⁻¹ *
          (if tensorWeight Q a=p.val then 1 else 0) := by
      simp [symmetricTensorInclusionReal, mul_ite]
    simp_rw [he, ← Finset.mul_sum, tensorWeight_count]
    apply (mul_left_cancel₀ hn)
    rw [mul_inv_cancel_left₀ hn]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ Q.choose p.val by positivity)]
  simpa [symmetricTensorInclusion] using congrArg Complex.ofReal hr

theorem symmetricTensor_weighted_column {R : Type*} [CommRing R]
    (f : ℂ →+* R) (Q : ℕ) (p : Fin (Q+1)) (m : ℕ → R) :
    (∑ a, f (symmetricTensorInclusion Q a p) * m (tensorWeight Q a)) =
      f (Real.sqrt (Q.choose p.val : ℝ) : ℂ) * m p.val := by
  have he (a : Fin Q → Fin 2) : f (symmetricTensorInclusion Q a p) * m (tensorWeight Q a) =
      f (symmetricTensorInclusion Q a p) * m p.val := by
    by_cases h : tensorWeight Q a=p.val
    · rw [h]
    · simp [symmetricTensorInclusion, symmetricTensorInclusionReal,h]
  simp_rw [he, ← Finset.sum_mul, ← map_sum, symmetricTensor_column_sum]

theorem tensorMatrix_polynomial {R : Type*} [CommRing R]
    (f : ℂ →+* R) (Q : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (u v : R) (b : Fin Q → Fin 2) :
    (∑ a, f (tensorMatrix Q A a b) *
      (v^(tensorWeight Q a)*u^(Q-tensorWeight Q a))) =
      (f (A 0 1)*u+f (A 1 1)*v)^(tensorWeight Q b) *
      (f (A 0 0)*u+f (A 1 0)*v)^(Q-tensorWeight Q b) := by
  have he (a : Fin Q → Fin 2) : f (tensorMatrix Q A a b) *
      (v^(tensorWeight Q a)*u^(Q-tensorWeight Q a)) =
      ∏ k, f (A (a k) (b k)) * (if a k=1 then v else u) := by
    rw [Finset.prod_mul_distrib, tensorWeight_product]
    simp [tensorMatrix]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun k x => f (A x (b k)) * (if x=1 then v else u))]
  have he' (k : Fin Q) : (∑ x : Fin 2, f (A x (b k)) * (if x=1 then v else u)) =
      if b k=1 then f (A 0 1)*u+f (A 1 1)*v else f (A 0 0)*u+f (A 1 0)*v := by
    have h : b k=0 ∨ b k=1 := by omega
    rcases h with h | h <;> simp [h, Fin.sum_univ_two]
  simp_rw [he']
  exact tensorWeight_product Q b _ _

theorem sourceSpinRepresentation_polynomial {R : Type*} [CommRing R]
    (f : ℂ →+* R) (Q : ℕ) (g : SourceSU2) (u v : R) (p : Fin (Q+1)) :
    (∑ q : Fin (Q+1), f (sourceSpinRepresentation Q g q p) *
      (f (Real.sqrt (Q.choose q.val : ℝ) : ℂ) * v^q.val*u^(Q-q.val))) =
      f (Real.sqrt (Q.choose p.val : ℝ) : ℂ) *
        (f (g.val 0 1)*u+f (g.val 1 1)*v)^p.val *
        (f (g.val 0 0)*u+f (g.val 1 0)*v)^(Q-p.val) := by
  have h := tensor_spin_intertwining Q g
  have hm := congrArg (fun M : Matrix (Fin Q → Fin 2) (Fin (Q+1)) ℂ =>
    ∑ a, f (M a p) * (v^(tensorWeight Q a)*u^(Q-tensorWeight Q a))) h
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul] at hm
  rw [Finset.sum_comm] at hm
  have hl (q : Fin (Q+1)) : (∑ a, f (symmetricTensorInclusion Q a q) *
      f (sourceSpinMatrix Q g q p) * (v^(tensorWeight Q a)*u^(Q-tensorWeight Q a))) =
      f (sourceSpinMatrix Q g q p) *
        (f (Real.sqrt (Q.choose q.val : ℝ) : ℂ)*v^q.val*u^(Q-q.val)) := by
    simp_rw [mul_right_comm _ (f (sourceSpinMatrix Q g q p)), ← Finset.sum_mul]
    rw [symmetricTensor_weighted_column f Q q (fun n => v^n*u^(Q-n))]
    ring
  simp_rw [hl] at hm
  rw [Finset.sum_comm] at hm
  have hr (b : Fin Q → Fin 2) : (∑ a, f (sourceTensorRepresentation Q g a b) *
      f (symmetricTensorInclusion Q b p) * (v^(tensorWeight Q a)*u^(Q-tensorWeight Q a))) =
      f (symmetricTensorInclusion Q b p) *
        ((f (g.val 0 1)*u+f (g.val 1 1)*v)^(tensorWeight Q b) *
        (f (g.val 0 0)*u+f (g.val 1 0)*v)^(Q-tensorWeight Q b)) := by
    simp_rw [mul_right_comm _ (f (symmetricTensorInclusion Q b p)), ← Finset.sum_mul]
    rw [show sourceTensorRepresentation Q g = tensorMatrix Q g.val from rfl,
      tensorMatrix_polynomial]
    ring
  simp_rw [hr] at hm
  rw [symmetricTensor_weighted_column f Q p (fun n =>
    (f (g.val 0 1)*u+f (g.val 1 1)*v)^n *
    (f (g.val 0 0)*u+f (g.val 1 0)*v)^(Q-n))] at hm
  simpa only [sourceSpinRepresentation, MonoidHom.coe_mk, OneHom.coe_mk, mul_assoc] using hm

end Laughlin.Rotation

end OAI
