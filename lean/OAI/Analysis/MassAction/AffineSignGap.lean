import Mathlib

namespace OAI

universe uIota

noncomputable section

namespace Problem326.Affine

open scoped BigOperators

/-- The elementary sup-norm / one-norm pairing estimate used by active affine labels. -/
theorem abs_sum_mul_le (ι : Type uIota) [Fintype ι]
    (u v : ι → ℝ) :
    |∑ i, u i * v i| ≤ ‖u‖ * ∑ i, |v i| := by
  classical
  calc
    |∑ i, u i * v i| ≤ ∑ i, |u i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |u i| * |v i| := by simp only [abs_mul]
    _ ≤ ∑ i, ‖u‖ * |v i| := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i) (abs_nonneg _)
    _ = ‖u‖ * ∑ i, |v i| := by rw [Finset.mul_sum]

/-- A nonzero linear comparison is stable under an error smaller than half its gap. -/
theorem sign_gap_of_abs_sub_lt {a b H : ℝ}
    (hab : |a - b| < |b| / 2) (hH : H ≤ |b| / 2) :
    (0 < a ↔ 0 < b) ∧ (a < 0 ↔ b < 0) ∧ H ≤ |a| := by
  have hb : b ≠ 0 := by
    intro h
    simp only [h, abs_zero, zero_div] at hab
    exact (not_lt_of_ge (abs_nonneg _)) hab
  rcases lt_or_gt_of_ne hb with hb | hb
  · rw [abs_of_neg hb] at hab hH
    have ha : a < 0 := by
      have h := (abs_lt.mp hab).2
      linarith
    constructor
    · simp [not_lt_of_ge ha.le, not_lt_of_ge hb.le]
    constructor
    · simp [ha, hb]
    · rw [abs_of_neg ha]
      have h := (abs_lt.mp hab).2
      linarith
  · rw [abs_of_pos hb] at hab hH
    have ha : 0 < a := by
      have h := (abs_lt.mp hab).1
      linarith
    constructor
    · simp [ha, hb]
    constructor
    · simp [not_lt_of_ge ha.le, not_lt_of_ge hb.le]
    · rw [abs_of_pos ha]
      have h := (abs_lt.mp hab).1
      linarith

end Problem326.Affine

end

end OAI
