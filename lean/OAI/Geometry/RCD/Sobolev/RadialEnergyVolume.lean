import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! # Averaging the radial energy estimate on the half testing ball -/

namespace RegularPointCoordinates

theorem radial_fit_energy_volume_units {r W V N C D w E P Λ Θ e : ℝ}
    (hr : 0 < r) (hW : 0 < W) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (hPE : P ≤ E)
    (hV : V / W ≤ Λ) (hNW : N / W ≤ Θ)
    (he : e ≤ C * (V * (D * r * w * Real.sqrt E) ^ 2 / r ^ 2 + N * P * w ^ 2)) :
    W⁻¹ * e ≤ C * (Λ * D ^ 2 + Θ) * w ^ 2 * E := by
  have hcancel : V * (D * r * w * Real.sqrt E) ^ 2 / r ^ 2 = V * D ^ 2 * w ^ 2 * E := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hE]
    field_simp [hr.ne']
  rw [hcancel] at he
  have hbound := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hW.le)
  have hfirst := mul_le_mul_of_nonneg_right hV
    (mul_nonneg (mul_nonneg (sq_nonneg D) (sq_nonneg w)) hE)
  have hsecond : (N / W) * P * w ^ 2 ≤ Θ * E * w ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hPE (div_nonneg hN hW.le)
    have hn := mul_le_mul_of_nonneg_right hNW hE
    exact mul_le_mul_of_nonneg_right (hm.trans hn) (sq_nonneg w)
  have hh := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hC
  apply hbound.trans
  convert hh using 1 <;> ring

end RegularPointCoordinates

end OAI
