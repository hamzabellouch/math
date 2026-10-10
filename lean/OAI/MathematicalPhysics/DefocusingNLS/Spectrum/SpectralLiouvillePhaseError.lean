import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvillePhaseApprox
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBConstruction

namespace OAI

/-! Real action comparison for the exact Liouville momentum. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_phase_error (sign h b eta omega gamma R E : ℝ)
    (hs : sign^2=1) (hR : 0<R) (hRE : R≤E) (chi : ℂ) (hchi : ‖chi‖=1)
    (hF : ∀ t ∈ Icc R E, 0<sign*homogeneousSpectralLocalizationFrequency h b eta omega t) :
    |(spectralWKBPhase R chi (spectralLiouvilleMomentum sign h b eta omega gamma) E).re-
      chi.re*(∫ t in R..E, Real.sqrt
        (sign*homogeneousSpectralLocalizationFrequency h b eta omega t))|≤
      |gamma| * (∫ t in R..E, 1/Real.sqrt
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
  have hpI : IntervalIntegrable p volume R E := hp.intervalIntegrable_of_Icc hRE
  have hqI : IntervalIntegrable (fun t => (q t : ℂ)) volume R E :=
    (Complex.continuous_ofReal.comp_continuousOn hq).intervalIntegrable_of_Icc hRE
  have heq : chi*(∫ t in R..E, p t)-chi*((∫ t in R..E, q t : ℝ) : ℂ)=
      chi*(∫ t in R..E, p t-(q t : ℂ)) := by
    rw [intervalIntegral.integral_sub hpI hqI,intervalIntegral.integral_ofReal]
    ring
  have ha := Complex.abs_re_le_norm
    (chi*(∫ t in R..E, p t)-chi*((∫ t in R..E, q t : ℝ) : ℂ))
  have hre : (chi*(∫ t in R..E, p t)-chi*((∫ t in R..E, q t : ℝ) : ℂ)).re=
      (spectralWKBPhase R chi p E).re-chi.re*(∫ t in R..E, q t) := by
    simp only [spectralWKBPhase,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero]
  rw [hre] at ha
  calc
    _ ≤ ‖chi*(∫ t in R..E, p t)-chi*((∫ t in R..E, q t : ℝ) : ℂ)‖ := ha
    _ = ‖∫ t in R..E, p t-(q t : ℂ)‖ := by rw [heq,norm_mul,hchi,one_mul]
    _ ≤ _ := spectralLiouville_phase_integral_error sign h b eta omega gamma R E hs hR hRE hF

end DefocusingNLS

end OAI
