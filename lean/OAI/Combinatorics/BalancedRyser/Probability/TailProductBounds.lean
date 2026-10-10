import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI

namespace Balanced.TailProduct

open scoped BigOperators

theorem neg_log_one_sub_le_twice {x : ℝ} (hx : 0 ≤ x) (hhalf : x ≤ 1 / 2) :
    -Real.log (1 - x) ≤ 2 * x := by
  have hp : 0 < 1 - x := by linarith
  have hi : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    apply (sub_le_iff_le_add).2
    apply (inv_le_iff_one_le_mul₀ hp).2
    nlinarith [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)]
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hl
  exact hl.trans hi

theorem inv_one_sub_le_exp_twice {x : ℝ} (hx : 0 ≤ x) (hhalf : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  apply Real.le_exp_of_log_le
  rw [Real.log_inv]
  exact neg_log_one_sub_le_twice hx hhalf

theorem prod_inv_one_sub_le_exp_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hhalf : ∀ i ∈ s, x i ≤ 1 / 2) :
    (∏ i ∈ s, (1 - x i)⁻¹) ≤ Real.exp (2 * ∑ i ∈ s, x i) := by
  calc
    (∏ i ∈ s, (1 - x i)⁻¹) ≤ ∏ i ∈ s, Real.exp (2 * x i) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact inv_nonneg.mpr (by linarith [hhalf i hi])
      · intro i hi
        exact inv_one_sub_le_exp_twice (hx i hi) (hhalf i hi)
    _ = Real.exp (2 * ∑ i ∈ s, x i) := by
      rw [← Real.exp_sum, Finset.mul_sum]

theorem prod_inv_one_sub_le_exp_half {ι : Type*} (t : Finset ι) (x : ι → ℝ)
    (s : ℕ) (hx : ∀ i ∈ t, 0 ≤ x i) (hhalf : ∀ i ∈ t, x i ≤ 1 / 2)
    (hsum : ∑ i ∈ t, x i ≤ (s : ℝ) / 4) :
    (∏ i ∈ t, (1 - x i)⁻¹) ≤ Real.exp ((s : ℝ) / 2) := by
  refine (prod_inv_one_sub_le_exp_sum t x hx hhalf).trans ?_
  apply Real.exp_le_exp.mpr
  linarith

end Balanced.TailProduct

end OAI
