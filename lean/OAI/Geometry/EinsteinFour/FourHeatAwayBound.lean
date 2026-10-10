import OAI.Geometry.EinsteinFour.FourHeatGaussianMoments

namespace OAI

/-! The Gaussian derivative scale is uniformly O(t) away from the center.
This is the bound used for the normal-chart cutoff commutator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour

noncomputable section

theorem fourHeatGaussian_weighted_inverse_time (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    ‖x‖ ^ 8 * (fourHeatGaussian t x / t) ≤ (384 / Real.pi ^ 2) * t := by
  let z := ‖x‖ ^ 2 / (4 * t)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hb : z ^ 4 * Real.exp (-z) ≤ 24 := by
    simpa only [show ((4 : ℕ).factorial : ℝ) = 24 by norm_num] using
      fourHeatPolynomial_absorption 4 z hz
  have he : ‖x‖ ^ 8 * (fourHeatGaussian t x / t) =
      ((16 / Real.pi ^ 2) * t) * (z ^ 4 * Real.exp (-z)) := by
    have harg : -(4 * t)⁻¹ * ‖x‖ ^ 2 = -z := by dsimp [z]; ring
    unfold fourHeatGaussian
    rw [harg]
    dsimp [z]
    field_simp
    ring
  rw [he]
  calc
    _ ≤ ((16 / Real.pi ^ 2) * t) * 24 :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem fourHeatGaussian_away_inverse_time (r t : ℝ) (hr : 0 < r) (ht : 0 < t)
    (x : FourSpace) (hx : r ≤ ‖x‖) :
    fourHeatGaussian t x / t ≤ (384 / (Real.pi ^ 2 * r ^ 8)) * t := by
  have hpow : r ^ 8 ≤ ‖x‖ ^ 8 := pow_le_pow_left₀ hr.le hx 8
  have hG : 0 ≤ fourHeatGaussian t x / t := div_nonneg (fourHeatGaussian_pos t ht x).le ht.le
  have hb : r ^ 8 * (fourHeatGaussian t x / t) ≤ (384 / Real.pi ^ 2) * t :=
    (mul_le_mul_of_nonneg_right hpow hG).trans (fourHeatGaussian_weighted_inverse_time t ht x)
  calc
    _ ≤ ((384 / Real.pi ^ 2) * t) / r ^ 8 :=
      (le_div_iff₀ (pow_pos hr 8)).mpr (by simpa only [mul_comm] using hb)
    _ = _ := by field_simp

end
end PositiveEinsteinFour.Geometry

end OAI
