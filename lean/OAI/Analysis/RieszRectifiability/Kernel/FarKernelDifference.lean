import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem inverse_pow_difference_le (q : ℕ) (a b r : ℝ)
    (hr : 0 < r) (ha : r ≤ a) (hb : r ≤ b) :
    |(a ^ (q + 1))⁻¹ - (b ^ (q + 1))⁻¹| ≤
      (q + 1 : ℝ) * |a - b| * (r ^ (q + 2))⁻¹ := by
  have ha0 : 0 < a := lt_of_lt_of_le hr ha
  have hb0 : 0 < b := lt_of_lt_of_le hr hb
  have hInv : |a⁻¹ - b⁻¹| ≤ |a - b| / r ^ 2 := by
    rw [inv_sub_inv ha0.ne' hb0.ne', abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hr)
    simpa only [pow_two] using! mul_le_mul ha hb hr.le ha0.le
  have hmax : max |a⁻¹| |b⁻¹| ≤ r⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr ha0), abs_of_pos (inv_pos.mpr hb0)]
    exact max_le (by simpa only [one_div] using! one_div_le_one_div_of_le hr ha)
      (by simpa only [one_div] using! one_div_le_one_div_of_le hr hb)
  calc
    _ = |(a⁻¹) ^ (q + 1) - (b⁻¹) ^ (q + 1)| := by rw [inv_pow, inv_pow]
    _ ≤ |a⁻¹ - b⁻¹| * (q + 1 : ℝ) * max |a⁻¹| |b⁻¹| ^ q := by
      simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using!
        abs_pow_sub_pow_le (a⁻¹) (b⁻¹) (q + 1)
    _ ≤ (|a - b| / r ^ 2) * (q + 1 : ℝ) * (r⁻¹) ^ q := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hInv (by positivity)
      · exact pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hmax q
      · positivity
      · positivity
    _ = _ := by
      rw [pow_add, inv_pow]
      field_simp

theorem inverseDistancePow_far_difference {d : ℕ} (m : ℕ) (a x y : Ambient d)
    (hy : 0 < dist a y) (hfar : 2 * dist x a ≤ dist a y) :
    |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y| ≤
      (m + 1 : ℝ) * 2 ^ (m + 2) * dist x a * inverseDistancePow (m + 2) a y := by
  have hhalf : dist a y / 2 ≤ dist x y := by
    have ht := dist_triangle a x y
    rw [dist_comm a x] at ht
    linarith
  have h := inverse_pow_difference_le m (dist x y) (dist a y) (dist a y / 2)
    (by positivity) hhalf (by linarith)
  have hdist := abs_dist_sub_le x a y
  unfold inverseDistancePow
  calc
    _ ≤ (m + 1 : ℝ) * |dist x y - dist a y| * ((dist a y / 2) ^ (m + 2))⁻¹ := h
    _ ≤ (m + 1 : ℝ) * dist x a * ((dist a y / 2) ^ (m + 2))⁻¹ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist (by positivity))
        (by positivity)
    _ = _ := by
      rw [div_pow, inv_div]
      ring

end

end RieszRectifiability

end OAI
