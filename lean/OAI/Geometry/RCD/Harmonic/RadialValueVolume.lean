import OAI.Geometry.RCD.Harmonic.RadialVolumeUnits

namespace OAI

/-! # Averaging the transferred Poisson radial values -/

namespace RegularPointCoordinates

/-- A source-to-volume ratio and the same scalar fit bound control the
Poisson value error in the radial length unit. -/
theorem radial_fit_value_volume_units {r W M C B D w E Θ e : ℝ}
    (hW : 0 < W) (hC : 0 ≤ C) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hM : M / W ≤ Θ * E)
    (he : e ≤ 2 * (W * (D * r * w * Real.sqrt E) ^ 2) +
      2 * (C * w ^ 2) * (M * (B * (64 * r) ^ 2))) :
    W⁻¹ * e ≤ (2 * D ^ 2 + 8192 * C * B * Θ) * (r * w) ^ 2 * E := by
  have hh := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hW.le)
  have hm := mul_le_mul_of_nonneg_left hM
    (show 0 ≤ 8192 * C * B * (r * w) ^ 2 by positivity)
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hE] at hh
  have hcalc : W⁻¹ * (2 * (W * (D ^ 2 * r ^ 2 * w ^ 2 * E)) +
      2 * (C * w ^ 2) * (M * (B * (64 * r) ^ 2))) =
        2 * D ^ 2 * (r * w) ^ 2 * E + 8192 * C * B * (r * w) ^ 2 * (M / W) := by
    field_simp [hW.ne']
    ring
  rw [hcalc] at hh
  apply hh.trans
  calc
    _ ≤ 2 * D ^ 2 * (r * w) ^ 2 * E +
        8192 * C * B * (r * w) ^ 2 * (Θ * E) := add_le_add le_rfl hm
    _ = _ := by ring

end RegularPointCoordinates

end OAI
