import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleResidualContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBSqrtApproximation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBPhaseIntegral

namespace OAI

/-! The complex action differs from the real action by a uniformly integrable
error, with its imaginary constant displayed explicitly. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_phase_pointwise (sign h b eta omega gamma r : ℝ)
    (hs : sign^2=1)
    (hF : 0<sign*homogeneousSpectralLocalizationFrequency h b eta omega r) :
    ‖spectralLiouvilleMomentum sign h b eta omega gamma r-
      (Real.sqrt (sign*homogeneousSpectralLocalizationFrequency h b eta omega r) : ℂ)‖≤
      |gamma|/Real.sqrt (sign*homogeneousSpectralLocalizationFrequency h b eta omega r) := by
  have hsign : |sign|=1 := by nlinarith [sq_abs sign,abs_nonneg sign]
  have he : spectralWKBSquaredMomentum sign
      (homogeneousSpectralLocalizationFrequency h b eta omega r) gamma=
      ((sign*homogeneousSpectralLocalizationFrequency h b eta omega r : ℝ) : ℂ)+
        Complex.I*((sign*gamma : ℝ) : ℂ) := by
    dsimp only [spectralWKBSquaredMomentum]
    push_cast
    ring
  dsimp only [spectralLiouvilleMomentum]
  rw [he]
  simpa only [abs_mul,hsign,one_mul] using spectralComplexSqrt_approx
    (sign*homogeneousSpectralLocalizationFrequency h b eta omega r) (sign*gamma) hF

theorem spectralLiouville_phase_integral_error
    (sign h b eta omega gamma R E : ℝ) (hs : sign^2=1) (hR : 0<R) (hRE : R≤E)
    (hF : ∀ t ∈ Icc R E, 0<sign*homogeneousSpectralLocalizationFrequency h b eta omega t) :
    ‖∫ t in R..E, spectralLiouvilleMomentum sign h b eta omega gamma t-
      (Real.sqrt (sign*homogeneousSpectralLocalizationFrequency h b eta omega t) : ℂ)‖≤
      |gamma| *(∫ t in R..E, 1/Real.sqrt
        (sign*homogeneousSpectralLocalizationFrequency h b eta omega t)) := by
  let p := spectralLiouvilleMomentum sign h b eta omega gamma
  let q := fun t => Real.sqrt (sign*homogeneousSpectralLocalizationFrequency h b eta omega t)
  have hp : ContinuousOn p (Icc R E) := fun t ht =>
    (spectralLiouvilleMomentum_hasDerivAt sign h b eta omega gamma t
      (hR.trans_le ht.1) (hF t ht)).continuousAt.continuousWithinAt
  have hFc : ContinuousOn (homogeneousSpectralLocalizationFrequency h b eta omega) (Icc R E) :=
    fun t ht => (homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t
      (hR.trans_le ht.1)).continuousAt.continuousWithinAt
  have hq : ContinuousOn q (Icc R E) :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul hFc)
  have hi : ContinuousOn (fun t => p t-(q t : ℂ)) (Icc R E) :=
    hp.sub (Complex.continuous_ofReal.comp_continuousOn hq)
  have hqn (t : ℝ) (ht : t ∈ Icc R E) : q t≠0 := (Real.sqrt_pos.2 (hF t ht)).ne'
  have hqc : ContinuousOn (fun t => |gamma| *(1/q t)) (Icc R E) :=
    continuousOn_const.mul (continuousOn_const.div hq hqn)
  calc
    _ ≤ ∫ t in R..E, ‖p t-(q t : ℂ)‖ := intervalIntegral.norm_integral_le_integral_norm hRE
    _ ≤ ∫ t in R..E, |gamma| *(1/q t) := intervalIntegral.integral_mono_on hRE
      (hi.norm.intervalIntegrable_of_Icc hRE) (hqc.intervalIntegrable_of_Icc hRE)
      (fun t ht => by
        have hb := spectralLiouville_phase_pointwise sign h b eta omega gamma t hs (hF t ht)
        simpa only [div_eq_mul_inv,one_mul] using hb)
    _ = _ := intervalIntegral.integral_const_mul _ _

end DefocusingNLS

end OAI
