import OAI.Geometry.RCD.Harmonic.RadialVolumeUnits

namespace OAI

/-! # Removing radius and volume units from the covector fit step -/

namespace RegularPointCoordinates

theorem radial_sqrt_volume_ratio {n : ℕ} {r theta omega V W : ℝ}
    (hr : 0 < r) (htheta : 0 < theta) (homega : 0 < omega) (hV0 : 0 ≤ V)
    (hV : |V / (omega * r ^ n) - 1| ≤ 1 / 4)
    (hW : |W / (omega * (theta * r) ^ n) - 1| ≤ 1 / 4) :
    Real.sqrt V / Real.sqrt W ≤ Real.sqrt ((5 / 3 : ℝ) * (theta ^ n)⁻¹) := by
  rw [← Real.sqrt_div hV0]
  exact Real.sqrt_le_sqrt (radial_fraction_volume_ratio hr htheta homega hV hW)

/-- The actual covector error has one coefficient independent of the
center and dyadic scale; its only variable source is sqrt(P) times the
norm of the covector in the current normalizing frame. -/
theorem radial_covector_fit_natural_units {s theta V Lambda A D N W Q b E F : ℝ}
    (hs : 0 < s) (htheta : 0 < theta) (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hb : 0 ≤ b) (hVL : V ≤ Lambda) (hratio : N / W ≤ D)
    (hstep : F ≤ (V + (1 / 2 : ℝ) * theta * Real.sqrt theta) / (theta * (s / 64)) *
      Real.sqrt (W⁻¹ * (A * s ^ 2 * (N * Q)) * b ^ 2) +
      (1 / 2 : ℝ) * Real.sqrt theta * E) :
    F ≤ (1 / 2 : ℝ) * Real.sqrt theta * E +
      (64 / theta) * (Lambda + (1 / 2 : ℝ) * theta * Real.sqrt theta) *
        Real.sqrt (A * D) * Real.sqrt Q * b := by
  have hroot := radial_sqrt_error_bound hs.le (mul_nonneg hQ (sq_nonneg b)) hA hD hratio
  have he : W⁻¹ * (A * s ^ 2 * (N * (Q * b ^ 2))) =
      W⁻¹ * (A * s ^ 2 * (N * Q)) * b ^ 2 := by ring
  rw [he, Real.sqrt_mul hQ, Real.sqrt_sq hb] at hroot
  have hcoef : (V + (1 / 2 : ℝ) * theta * Real.sqrt theta) / (theta * (s / 64)) ≤
      (Lambda + (1 / 2 : ℝ) * theta * Real.sqrt theta) / (theta * (s / 64)) :=
    div_le_div_of_nonneg_right (add_le_add hVL (le_refl _)) (by positivity)
  have hLambda : 0 ≤ Lambda := hV.trans hVL
  have hh := mul_le_mul hcoef hroot (Real.sqrt_nonneg _)
    (by positivity : 0 ≤ (Lambda + (1 / 2 : ℝ) * theta * Real.sqrt theta) / (theta * (s / 64)))
  apply hstep.trans
  calc
    _ ≤ (Lambda + (1 / 2 : ℝ) * theta * Real.sqrt theta) / (theta * (s / 64)) *
        (s * Real.sqrt (A * D) * (Real.sqrt Q * b)) +
        (1 / 2 : ℝ) * Real.sqrt theta * E := add_le_add hh (le_refl _)
    _ = _ := by field_simp; ring

end RegularPointCoordinates

end OAI
