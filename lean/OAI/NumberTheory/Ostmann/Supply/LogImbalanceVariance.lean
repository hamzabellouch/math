import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace OAI

/-! # Logarithmic imbalance from the collision variance -/

namespace Ostmann
open scoped BigOperators

private theorem log_sq_le_four_variance_of_one_le (t : ℝ) (ht : 1 ≤ t) :
    (Real.log t) ^ 2 ≤ 4 * (t + t⁻¹ - 2) := by
  have ht0 : 0 < t := by linarith
  let s := Real.sqrt t
  have hs : 1 ≤ s := Real.one_le_sqrt.mpr ht
  have hs0 : 0 < s := by linarith
  have hs2 : s ^ 2 = t := Real.sq_sqrt ht0.le
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlog : Real.log t ≤ 2 * (s - 1) := by
    have hh := Real.log_le_sub_one_of_pos hs0
    have he := Real.log_sqrt ht0.le
    change Real.log s = Real.log t / 2 at he
    linarith
  have hsq : (Real.log t) ^ 2 ≤ 4 * (s - 1) ^ 2 := by nlinarith
  have hid : t * (t + t⁻¹ - 2 - (s - 1) ^ 2) = (s - 1) ^ 2 * (2 * s + 1) := by
    calc
      _ = s ^ 2 * (s ^ 2 + (s ^ 2)⁻¹ - 2 - (s - 1) ^ 2) := by rw [hs2]
      _ = _ := by field_simp; ring
  have hvar : (s - 1) ^ 2 ≤ t + t⁻¹ - 2 := by
    have hp : 0 ≤ t * (t + t⁻¹ - 2 - (s - 1) ^ 2) := by
      rw [hid]
      exact mul_nonneg (sq_nonneg _) (by linarith)
    have hd := nonneg_of_mul_nonneg_right hp ht0
    linarith
  linarith

theorem log_sq_le_four_variance (t : ℝ) (ht : 0 < t) :
    (Real.log t) ^ 2 ≤ 4 * (t + t⁻¹ - 2) := by
  by_cases h : 1 ≤ t
  · exact log_sq_le_four_variance_of_one_le t h
  · have hinv : 1 ≤ t⁻¹ := by
      simpa only [one_div, inv_one] using
        div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num) ht (le_of_not_ge h)
    have hh := log_sq_le_four_variance_of_one_le t⁻¹ hinv
    simpa only [Real.log_inv, neg_sq, inv_inv, add_comm] using hh

/-- A finite Cauchy--Schwarz form ready for the actual prime collision budget.
A harmless absolute factor four avoids any additional analytic theorem. -/
theorem logarithmic_imbalance_budget (P : Finset ℕ) (κ : ℕ → ℝ)
    (hP : ∀ p ∈ P, 1 < p) (hκ : ∀ p ∈ P, 0 < κ p) :
    (∑ p ∈ P, |Real.log (κ p)| / p) ^ 2 ≤
      (4 * ∑ p ∈ P, (κ p + (κ p)⁻¹ - 2) * Real.log p / p) *
        ∑ p ∈ P, 1 / ((p : ℝ) * Real.log p) := by
  rw [Finset.mul_sum P (fun p => (κ p + (κ p)⁻¹ - 2) * Real.log p / p) 4]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul P
  · intro p hp
    have hv : 0 ≤ κ p + (κ p)⁻¹ - 2 := by
      nlinarith [log_sq_le_four_variance (κ p) (hκ p hp), sq_nonneg (Real.log (κ p))]
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hP p hp)
    positivity
  · intro p hp
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hP p hp)
    positivity
  · intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_trans Nat.zero_lt_one (hP p hp))
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hP p hp)
    have hh := log_sq_le_four_variance (κ p) (hκ p hp)
    rw [div_pow, sq_abs]
    apply (div_le_iff₀ (sq_pos_of_pos hp0)).mpr
    convert hh using 1
    field_simp

end Ostmann

end OAI
