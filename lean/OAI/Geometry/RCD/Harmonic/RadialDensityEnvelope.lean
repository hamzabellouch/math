import OAI.Geometry.RCD.Harmonic.RadialContractionFactor

namespace OAI

/-! # A uniform envelope for the small-time radial densities -/

namespace RegularPointCoordinates

theorem radialContractionDensity_le {κ D t : ℝ} (n : ℕ) (hκ : 0 ≤ κ)
    (_ht : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    radialContractionDensity n κ D t ≤ 2 ^ n * Real.exp (κ * D ^ 2 / 6) := by
  have hd : 0 < (1 - t) ^ n := pow_pos (by linarith) _
  have hnum : Real.exp (κ * D ^ 2 * (1 - (1 - t) ^ 2) / 6) ≤
      Real.exp (κ * D ^ 2 / 6) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (mul_nonneg hκ (sq_nonneg D)) (sq_nonneg (1 - t))]
  have hprod : 1 ≤ (2 : ℝ) ^ n * (1 - t) ^ n := by
    rw [← mul_pow]
    exact one_le_pow₀ (by linarith)
  apply (div_le_iff₀ hd).mpr
  have hh := mul_le_mul_of_nonneg_left hprod (Real.exp_pos (κ * D ^ 2 / 6)).le
  nlinarith

end RegularPointCoordinates

end OAI
