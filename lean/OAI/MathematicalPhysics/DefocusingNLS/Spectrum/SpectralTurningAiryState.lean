import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningState
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningCoefficient
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarReflection
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarFlux

namespace OAI

/-! Reflected turning-point coordinates put the forbidden side on the
positive Airy half-line. Reflection reverses the conserved flux. -/

namespace DefocusingNLS

noncomputable def spectralTurningAiryState (r₀ d s : ℝ)
    (q : ℝ → ℂ × ℂ) : ℝ → ℂ × ℂ :=
  spectralScalarReflect 0 0 (spectralTurningState r₀ d s q)

theorem spectralTurningAiryState_continuous (r₀ d s : ℝ)
    (q : ℝ → ℂ × ℂ) (hq : Continuous q) :
    Continuous (spectralTurningAiryState r₀ d s q) := by
  apply spectralScalarReflect_continuous
  have hc : Continuous (fun t => q (r₀ + d * t)) :=
    hq.comp (continuous_const.add (continuous_const.mul continuous_id))
  exact (hc.fst.div_const (s : ℂ)).prodMk (hc.snd.const_mul (s : ℂ))

theorem spectralTurningAiryState_hasDerivAt
    (h b eta omega gamma r₀ d s t : ℝ) (hs : s ≠ 0) (hsq : s^2 = d)
    (q : ℝ → ℂ × ℂ)
    (hq : HasDerivAt q (spectralScalarField
      ((homogeneousSpectralLocalizationFrequency h b eta omega (r₀ - d*t) : ℂ) +
        Complex.I*(gamma : ℂ)) (q (r₀ - d*t))) (r₀ - d*t)) :
    HasDerivAt (spectralTurningAiryState r₀ d s q)
      (spectralScalarField
        (spectralTurningCoefficient h b eta omega gamma r₀ d (-t))
        (spectralTurningAiryState r₀ d s q t)) t := by
  have he : r₀ + d * (-t) = r₀ - d*t := by ring
  have hd := spectralTurningState_hasDerivAt r₀ d s (-t) hs hsq q
    ((homogeneousSpectralLocalizationFrequency h b eta omega (r₀-d*t) : ℂ) +
      Complex.I*(gamma : ℂ)) (by simpa only [he] using hq)
  have hr := spectralScalarReflect_hasDerivAt 0 0 t
    (spectralTurningState r₀ d s q)
    ((d : ℂ)^2*((homogeneousSpectralLocalizationFrequency h b eta omega (r₀-d*t) : ℂ) +
      Complex.I*(gamma : ℂ))) (by simpa only [zero_add,zero_sub] using hd)
  simpa only [spectralTurningAiryState,spectralTurningCoefficient,
    Complex.ofReal_pow,he] using hr

theorem spectralTurningAiryState_flux (r₀ d s t : ℝ) (hs : s ≠ 0)
    (q : ℝ → ℂ × ℂ) :
    spectralScalarFlux (spectralTurningAiryState r₀ d s q t) =
      -spectralScalarFlux (q (r₀-d*t)) := by
  simp only [spectralScalarFlux,spectralTurningAiryState,spectralScalarReflect,
    zero_add,zero_sub,mul_neg,Complex.neg_im]
  rw [spectralTurningState_flux r₀ d s (-t) hs q]
  simp only [mul_neg,sub_eq_add_neg]

end DefocusingNLS

end OAI
