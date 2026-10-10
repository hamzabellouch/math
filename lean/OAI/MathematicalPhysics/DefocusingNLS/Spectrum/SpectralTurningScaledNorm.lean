import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningAiryState
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleFrequencyJet

namespace OAI

/-! The turning-point scaling preserves the shell norm when its frequency
weight is scaled as well. -/

namespace DefocusingNLS

theorem spectralComplexSqrt_scaled_weight (d : ℝ) (hd : 0 ≤ d) (z : ℂ) :
    Real.sqrt d * Real.sqrt ‖Complex.sqrt z‖ =
      Real.sqrt (Real.sqrt ‖(d : ℂ)^2 * z‖) := by
  have hz : Real.sqrt ‖z‖ = ‖Complex.sqrt z‖ := by
    have hsq := spectralComplexSqrt_norm_sq z
    have hrt := Real.sq_sqrt (norm_nonneg z)
    nlinarith [Real.sqrt_nonneg ‖z‖,norm_nonneg (Complex.sqrt z)]
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd,
    Real.sqrt_mul (sq_nonneg d),Real.sqrt_sq hd,hz,Real.sqrt_mul hd]

theorem spectralShellNorm_scale (s k : ℝ) (hs : 0 < s) (hk : 0 < k) (u : ℂ × ℂ) :
    spectralShellNorm (s*k) (u.1/(s : ℂ),-(s : ℂ)*u.2) = spectralShellNorm k u := by
  simp only [spectralShellNorm,norm_div,norm_mul,norm_neg,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  field_simp

theorem spectralShellNorm_controls_norm (a b k : ℝ) (ha : 0 < a)
    (hak : a ≤ k) (hkb : k ≤ b) (u : ℂ × ℂ) :
    ‖u‖ ≤ max a⁻¹ b * spectralShellNorm k u := by
  have hk : 0 < k := ha.trans_le hak
  have hN := spectralShellNorm_nonneg k hk.le u
  have hf := spectralShellNorm_value k hk u
  have hs := spectralShellNorm_slope k hk u
  rw [Prod.norm_def]
  apply max_le
  · calc
      ‖u.1‖ ≤ spectralShellNorm k u / k := hf
      _ = k⁻¹ * spectralShellNorm k u := by ring
      _ ≤ a⁻¹ * spectralShellNorm k u :=
        mul_le_mul_of_nonneg_right (inv_anti₀ ha hak) hN
      _ ≤ max a⁻¹ b * spectralShellNorm k u :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hN
  · exact hs.trans (mul_le_mul_of_nonneg_right (hkb.trans (le_max_right _ _)) hN)

theorem spectralTurning_scaled_weight
    (h b eta omega gamma r₀ d xi : ℝ) (hd : 0 ≤ d) :
    Real.sqrt d * Real.sqrt ‖spectralLiouvilleMomentum 1 h b eta omega gamma (r₀+d*xi)‖ =
      Real.sqrt (Real.sqrt ‖spectralTurningCoefficient h b eta omega gamma r₀ d xi‖) := by
  simpa only [spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,
    one_mul,spectralTurningCoefficient,Complex.ofReal_pow] using
    spectralComplexSqrt_scaled_weight d hd
      ((homogeneousSpectralLocalizationFrequency h b eta omega (r₀+d*xi) : ℂ) +
        Complex.I*(gamma : ℂ))


theorem spectralTurningState_shell_norm (r₀ d s xi k : ℝ) (hs : 0 < s) (hk : 0 < k)
    (q : ℝ → ℂ × ℂ) :
    spectralShellNorm (s*k) (spectralTurningState r₀ d s q xi) =
      spectralShellNorm k (q (r₀+d*xi)) := by
  simp only [spectralShellNorm,spectralTurningState,norm_div,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  field_simp

end DefocusingNLS

end OAI
