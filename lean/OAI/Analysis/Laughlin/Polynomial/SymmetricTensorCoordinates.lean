import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases
import OAI.Analysis.Laughlin.Spin.TensorAction

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def tensorBits (Q : ℕ) (a : Fin Q → Fin 2) : Finset (Fin Q) :=
  Finset.univ.filter (fun i => a i=1)
noncomputable def subsetTensorBits (Q : ℕ) (s : Finset (Fin Q)) : Fin Q → Fin 2 :=
  fun i => if i ∈ s then 1 else 0

noncomputable def tensorSubsetEquiv (Q : ℕ) : (Fin Q → Fin 2) ≃ Finset (Fin Q) where
  toFun := tensorBits Q
  invFun := subsetTensorBits Q
  left_inv a := by
    funext i
    simp only [subsetTensorBits,tensorBits,Finset.mem_filter,Finset.mem_univ,true_and]
    have hi : a i=0 ∨ a i=1 := by omega
    rcases hi with hi | hi <;> simp [hi]
  right_inv s := by
    ext i
    simp [tensorBits,subsetTensorBits]

noncomputable def tensorWeight (Q : ℕ) (a : Fin Q → Fin 2) : ℕ := (tensorBits Q a).card

 theorem tensorWeight_count (Q p : ℕ) :
    (∑ a : Fin Q → Fin 2, if tensorWeight Q a=p then (1 : ℝ) else 0) = Q.choose p := by
  classical
  have he : (∑ a : Fin Q → Fin 2, if tensorWeight Q a=p then (1 : ℝ) else 0) =
      ∑ s : Finset (Fin Q), if s.card=p then (1 : ℝ) else 0 :=
    (tensorSubsetEquiv Q).sum_comp (fun s => if s.card=p then (1 : ℝ) else 0)
  rw [he]
  have hs : (Finset.univ.filter (fun s : Finset (Fin Q) => s.card=p)) =
      (Finset.univ : Finset (Fin Q)).powersetCard p := by
    ext s
    simp [Finset.mem_powersetCard]
  rw [← Finset.sum_filter]
  rw [hs]
  simp

noncomputable def symmetricTensorInclusionReal (Q : ℕ) :
    Matrix (Fin Q → Fin 2) (Fin (Q+1)) ℝ :=
  fun a p => if tensorWeight Q a=p.val then (Real.sqrt (Q.choose p.val : ℝ))⁻¹ else 0

theorem symmetricTensorInclusionReal_isometry (Q : ℕ) :
    (symmetricTensorInclusionReal Q)ᵀ*symmetricTensorInclusionReal Q=1 := by
  classical
  ext p q
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,symmetricTensorInclusionReal]
  by_cases hpq : p=q
  · subst q
    rw [ite_eq_left rfl]
    have hn : (Q.choose p.val : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.choose_pos (by omega : p.val ≤ Q)))
    have he (a : Fin Q → Fin 2) :
        (if tensorWeight Q a=p.val then (Real.sqrt (Q.choose p.val : ℝ))⁻¹ else 0) *
        (if tensorWeight Q a=p.val then (Real.sqrt (Q.choose p.val : ℝ))⁻¹ else 0) =
        ((Real.sqrt (Q.choose p.val : ℝ))⁻¹)^2 * (if tensorWeight Q a=p.val then 1 else 0) := by
      split_ifs <;> ring
    simp_rw [he,← Finset.mul_sum,tensorWeight_count]
    rw [inv_pow,Real.sq_sqrt (by positivity),inv_mul_cancel₀ hn]
  · rw [ite_eq_right hpq]
    apply Finset.sum_eq_zero
    intro a ha
    have h : p.val ≠ q.val := fun h => hpq (Fin.ext h)
    split_ifs <;> simp_all

end Laughlin.Rotation

end OAI
