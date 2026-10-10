import OAI.Analysis.IrrationalRotation.Model.WeightedShift
import Mathlib.Tactic

namespace OAI

noncomputable section
open scoped ENNReal BigOperators
namespace Invariant233.WeightedShift

@[simp] theorem reindex_apply (e : Equiv.Perm ℤ) (ξ : Hilbert) (k : ℤ) :
    reindex e ξ k = ξ (e k) := rfl

@[simp] theorem shift_apply (m : ℤ) (ξ : Hilbert) (k : ℤ) :
    shift m ξ k = ξ (k - m) := rfl

@[simp] theorem diagonal_apply (w : Weight) (ξ : Hilbert) (k : ℤ) :
    diagonal w ξ k = w k * ξ k := rfl

@[simp] theorem operator_apply (w : Weight) (ξ : Hilbert) (k : ℤ) :
    operator w ξ k = w (k - 1) * ξ (k - 1) := rfl

theorem operator_pow_apply_add (w : Weight) (n : ℕ) (ξ : Hilbert) (k : ℤ) :
    (((operator w)^n) ξ) (k + n) =
      (∏ j ∈ Finset.range n, w (k + j)) * ξ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, operator_apply]
    have hk : k + (↑(n + 1) : ℤ) - 1 = k + n := by omega
    rw [hk, ih, Finset.prod_range_succ]
    ring

theorem operator_pow_apply (w : Weight) (n : ℕ) (ξ : Hilbert) (k : ℤ) :
    (((operator w)^n) ξ) k =
      (∏ j ∈ Finset.range n, w (k - n + j)) * ξ (k - n) := by
  simpa using operator_pow_apply_add w n ξ (k - n)

theorem norm_operator_pow_le (w : Weight) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hprod : ∀ k : ℤ, ‖∏ j ∈ Finset.range n, w (k + j)‖ ≤ B) :
    ‖(operator w)^n‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro ξ
  calc
    ‖((operator w)^n) ξ‖ ≤ ‖B • shift (n : ℤ) ξ‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro k
      simp only [operator_pow_apply, norm_mul, lp.coeFn_smul, Pi.smul_apply,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hB, shift_apply]
      exact mul_le_mul_of_nonneg_right (hprod (k - n)) (norm_nonneg _)
    _ = B * ‖ξ‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hB,
      (shift (n : ℤ)).norm_map]

theorem norm_product_le_norm_operator_pow (w : Weight) (n : ℕ) (k : ℤ) :
    ‖∏ j ∈ Finset.range n, w (k + j)‖ ≤ ‖(operator w)^n‖ := by
  let ξ : Hilbert := lp.single 2 k 1
  have hξ : ‖ξ‖ = 1 := by simp [ξ, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  have heval : (((operator w)^n) ξ) (k + n) =
      ∏ j ∈ Finset.range n, w (k + j) := by
    rw [operator_pow_apply_add]
    simp [ξ]
  calc
    ‖∏ j ∈ Finset.range n, w (k + j)‖ =
        ‖(((operator w)^n) ξ) (k + n)‖ := congrArg norm heval.symm
    _ ≤ ‖((operator w)^n) ξ‖ := lp.norm_apply_le_norm (by norm_num) _ _
    _ ≤ ‖(operator w)^n‖ * ‖ξ‖ := ((operator w)^n).le_opNorm ξ
    _ = ‖(operator w)^n‖ := by rw [hξ, mul_one]

@[simp] theorem orbitProduct_apply (w : Weight) (n : ℕ) (k : ℤ) :
    orbitProduct w n k = ∏ j ∈ Finset.range n, w (k + j) := rfl

theorem operator_pow_eq_shift_diagonal (w : Weight) (n : ℕ) :
    (operator w)^n =
      (shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap.comp
        (diagonal (orbitProduct w n)) := by
  ext ξ k
  exact operator_pow_apply w n ξ k

theorem norm_operator_pow (w : Weight) (n : ℕ) :
    ‖(operator w)^n‖ = ‖orbitProduct w n‖ := by
  apply le_antisymm
  · apply norm_operator_pow_le w n (norm_nonneg _)
    intro k
    exact lp.norm_apply_le_norm (by simp) (orbitProduct w n) k
  · apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro k
    exact norm_product_le_norm_operator_pow w n k

@[simp] theorem norm_operator (w : Weight) : ‖operator w‖ = ‖w‖ := by
  have h : orbitProduct w 1 = w := by ext k; simp [orbitProduct_apply]
  simpa [h] using norm_operator_pow w 1

@[simp] theorem operator_eq_zero_iff (w : Weight) : operator w = 0 ↔ w = 0 := by
  rw [← norm_eq_zero, norm_operator, norm_eq_zero]

end Invariant233.WeightedShift

end

end OAI
