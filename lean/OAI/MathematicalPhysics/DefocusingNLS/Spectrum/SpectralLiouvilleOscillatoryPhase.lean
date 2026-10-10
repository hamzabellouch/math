import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvillePhaseError

namespace OAI

/-! A bound for the whole positive-frequency phase, in either oscillatory
orientation, follows from the real phase integral. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_positive_phase_bound
    (h b eta omega gamma R E A : ℝ) (hR : 0 < R) (hRE : R ≤ E)
    (chi : ℂ) (hchi : ‖chi‖ = 1) (hchiRe : chi.re = 0)
    (hF : ∀ t ∈ Icc R E, 0 < homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hA : (∫ t in R..E, 1/Real.sqrt
      (homogeneousSpectralLocalizationFrequency h b eta omega t)) ≤ A) :
    ∀ r ∈ Icc R E,
      |(spectralWKBPhase R chi (spectralLiouvilleMomentum 1 h b eta omega gamma) r).re| ≤
        |gamma| * A := by
  have hFc : ContinuousOn (homogeneousSpectralLocalizationFrequency h b eta omega) (Icc R E) :=
    fun t ht => (homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t
      (hR.trans_le ht.1)).continuousAt.continuousWithinAt
  have hgc : ContinuousOn (fun t => 1/Real.sqrt
      (homogeneousSpectralLocalizationFrequency h b eta omega t)) (Icc R E) :=
    continuousOn_const.div (Real.continuous_sqrt.comp_continuousOn hFc)
      (fun t ht => (Real.sqrt_pos.mpr (hF t ht)).ne')
  intro r hr
  have hs : Icc R r ⊆ Icc R E := Icc_subset_Icc le_rfl hr.2
  have hp := spectralLiouville_phase_error 1 h b eta omega gamma R r (by norm_num)
    hR hr.1 chi hchi (fun t ht => by simpa only [one_mul] using hF t (hs ht))
  have hi : (∫ t in R..r, 1/Real.sqrt
      (homogeneousSpectralLocalizationFrequency h b eta omega t)) ≤ A := by
    apply le_trans _ hA
    exact intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
      (Filter.Eventually.of_forall (fun t => by positivity))
      (ContinuousOn.intervalIntegrable_of_Icc hRE hgc)
  apply le_trans _ (mul_le_mul_of_nonneg_left hi (abs_nonneg gamma))
  simpa only [one_mul,hchiRe,zero_mul,sub_zero] using hp

end DefocusingNLS

end OAI
