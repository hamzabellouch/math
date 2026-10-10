import Mathlib

namespace OAI

noncomputable section

namespace Problem313

/-- The logarithmic simplification used in the threshold-width estimate. -/
theorem log_odds_le_two_log_half_inv (ε : ℝ) (hε : 0 < ε)
    (hεhalf : ε < (1 / 2 : ℝ)) :
    Real.log ((1 - ε) / ε) ≤ 2 * Real.log (1 / (2 * ε)) := by
  have hnum : 0 < 1 - ε := by linarith
  have hden : 0 < 2 * ε := by positivity
  have hratio : (1 - ε) / ε ≤ (1 / (2 * ε)) ^ 2 := by
    rw [div_pow, one_pow]
    apply (div_le_div_iff₀ hε (sq_pos_of_pos hden)).2
    nlinarith [mul_nonneg (le_of_lt hε) (sq_nonneg (1 - 2 * ε))]
  have hlog := Real.log_le_log (div_pos hnum hε) hratio
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

/-- Multiplying the logarithmic estimate by a nonnegative constant. -/
theorem threshold_log_conversion (C ε w : ℝ) (hC : 0 ≤ C)
    (hε : 0 < ε) (hεhalf : ε < (1 / 2 : ℝ))
    (hw : w ≤ (2 * C) * Real.log ((1 - ε) / ε)) :
    w ≤ (4 * C) * Real.log (1 / (2 * ε)) := by
  calc
    w ≤ (2 * C) * Real.log ((1 - ε) / ε) := hw
    _ ≤ (2 * C) * (2 * Real.log (1 / (2 * ε))) :=
      mul_le_mul_of_nonneg_left (log_odds_le_two_log_half_inv ε hε hεhalf)
        (by positivity)
    _ = (4 * C) * Real.log (1 / (2 * ε)) := by ring

/-- The numerical constants relating the variance and threshold-width bounds. -/
theorem threshold_constant_conversion (t ε w : ℝ)
    (hε : 0 < ε) (hεhalf : ε < (1 / 2 : ℝ))
    (hw : w ≤ ((2 * (2 : ℝ) ^ 17) / t ^ 2) *
      Real.log ((1 - ε) / ε)) :
    w ≤ ((2 : ℝ) ^ 19 / t ^ 2) * Real.log (1 / (2 * ε)) := by
  have hC : 0 ≤ (2 : ℝ) ^ 17 / t ^ 2 := by positivity
  have hw' : w ≤ (2 * ((2 : ℝ) ^ 17 / t ^ 2)) *
      Real.log ((1 - ε) / ε) := by
    convert hw using 1; ring
  have h := threshold_log_conversion ((2 : ℝ) ^ 17 / t ^ 2) ε w hC hε hεhalf hw'
  convert h using 1; ring

end Problem313

end

end OAI
