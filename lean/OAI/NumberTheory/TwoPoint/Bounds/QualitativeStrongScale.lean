import OAI.NumberTheory.TwoPoint.Bounds.QualitativeSieveParameters

namespace OAI

/-! Final scale arithmetic in the qualitative rough-shift estimate. -/

namespace TwoPointCorrelations

open Filter

lemma eventually_strong_qualitative_frequency_gap :
    ∀ᶠ B : ℝ in atTop,
      (Real.log B / B ^ (9999 / 10000 : ℝ)) ^ (6 : ℕ) ≤
        (B ^ (-11 / 10 : ℝ)) ^ (5 : ℕ) := by
  have hs := (isLittleO_log_rpow_atTop
    (show 0 < (1 / 20 : ℝ) by norm_num)).bound (show 0 < (1 : ℝ) by norm_num)
  filter_upwards [eventually_ge_atTop 1, hs] with B hB hb
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hBp _), one_mul] at hb
  have hq : Real.log B / B ^ (9999 / 10000 : ℝ) ≤ B ^ (-9499 / 10000 : ℝ) := by
    calc
      _ ≤ B ^ (1 / 20 : ℝ) / B ^ (9999 / 10000 : ℝ) :=
        div_le_div_of_nonneg_right hb (by positivity)
      _ = _ := by rw [← Real.rpow_sub hBp]; norm_num
  calc
    _ ≤ (B ^ (-9499 / 10000 : ℝ)) ^ (6 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hq 6
    _ = B ^ (-28497 / 5000 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBp.le]
      norm_num
    _ ≤ B ^ (-11 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBp.le]
      norm_num

end TwoPointCorrelations

end OAI
