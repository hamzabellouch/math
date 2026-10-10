import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBSquareRoot
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBPotentialResidual

namespace OAI

/-! The exact first two momentum derivatives used in the WKB residual. -/

namespace DefocusingNLS

theorem spectralComplexSqrt_slope_hasDerivAt (Z d : ℝ → ℂ) (e : ℂ) (r : ℝ)
    (hZ : HasDerivAt Z (d r) r) (hd : HasDerivAt d e r) (hRe : 0<(Z r).re) :
    HasDerivAt (fun t => d t/(2*Complex.sqrt (Z t)))
      (e/(2*Complex.sqrt (Z r))-(d r)^2/(4*(Complex.sqrt (Z r))^3)) r := by
  have hp := spectralComplexSqrt_hasDerivAt Z (d r) r hZ hRe
  have hz : Z r≠0 := by intro he; rw [he] at hRe; norm_num at hRe
  have hp0 := spectralComplexSqrt_ne_zero (Z r) hz
  apply (hd.div (hp.const_mul 2) (mul_ne_zero (by norm_num) hp0)).congr_deriv
  field_simp [hp0]
  ring

noncomputable def spectralWKBSquaredMomentum (sign F gamma : ℝ) : ℂ :=
  (sign : ℂ)*((F : ℂ)+Complex.I*(gamma : ℂ))

theorem spectralWKBSquaredMomentum_re (sign F gamma : ℝ) :
    (spectralWKBSquaredMomentum sign F gamma).re=sign*F := by
  simp only [spectralWKBSquaredMomentum,Complex.mul_re,Complex.add_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero]

theorem spectralWKBSquaredMomentum_norm_lower (sign F gamma : ℝ)
    (hs : sign^2=1) : |F|≤‖spectralWKBSquaredMomentum sign F gamma‖ := by
  have hsign : |sign|=1 := by nlinarith [sq_abs sign,abs_nonneg sign]
  have he : |(spectralWKBSquaredMomentum sign F gamma).re|=|F| := by
    rw [spectralWKBSquaredMomentum_re,abs_mul,hsign,one_mul]
  rw [← he]
  exact Complex.abs_re_le_norm _

theorem spectralWKBSqrt_frequency_lower (sign F gamma : ℝ) (hs : sign^2=1) :
    Real.sqrt |F|≤‖Complex.sqrt (spectralWKBSquaredMomentum sign F gamma)‖ := by
  have hn := spectralWKBSquaredMomentum_norm_lower sign F gamma hs
  have hp := spectralComplexSqrt_norm_sq (spectralWKBSquaredMomentum sign F gamma)
  have hsq := Real.sq_sqrt (abs_nonneg F)
  nlinarith [Real.sqrt_nonneg |F|,norm_nonneg (Complex.sqrt (spectralWKBSquaredMomentum sign F gamma))]

end DefocusingNLS

end OAI
