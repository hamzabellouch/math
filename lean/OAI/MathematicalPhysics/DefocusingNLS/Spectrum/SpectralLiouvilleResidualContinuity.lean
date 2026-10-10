import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleResidual

namespace OAI

/-! Continuity of the actual complex WKB residual away from the turning point. -/

open Set
namespace DefocusingNLS

theorem spectralLiouvilleResidual_continuousOn
    (sign h b eta omega gamma a c : ℝ) (hs : sign^2=1)
    (ha : 0<a) (hF : ∀ t ∈ Icc a c,
      0<sign*homogeneousSpectralLocalizationFrequency h b eta omega t) :
    ContinuousOn (spectralLiouvilleResidual sign h b eta omega gamma) (Icc a c) ∧
    ContinuousOn (fun t => ‖spectralLiouvilleResidual sign h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum sign h b eta omega gamma t‖) (Icc a c) := by
  let p := spectralLiouvilleMomentum sign h b eta omega gamma
  let D := fun t => (sign : ℂ)*(spectralLiouvilleSlope eta t : ℂ)
  let E := fun t => (sign : ℂ)*(spectralLiouvilleSecond eta t : ℂ)
  have ht0 (t : ℝ) (ht : t ∈ Icc a c) : 0<t := ha.trans_le ht.1
  have hp : ContinuousOn p (Icc a c) := fun t ht =>
    (spectralLiouvilleMomentum_hasDerivAt sign h b eta omega gamma t (ht0 t ht)
      (hF t ht)).continuousAt.continuousWithinAt
  have hpn (t : ℝ) (ht : t ∈ Icc a c) : p t≠0 := by
    have hf : homogeneousSpectralLocalizationFrequency h b eta omega t≠0 := by
      intro he
      have := hF t ht
      rw [he,mul_zero] at this
      exact lt_irrefl _ this
    have hk := spectralWKBSqrt_frequency_lower sign
      (homogeneousSpectralLocalizationFrequency h b eta omega t) gamma hs
    have hkn := Real.sqrt_pos.2 (abs_pos.2 hf)
    exact norm_pos_iff.mp (lt_of_lt_of_le hkn hk)
  have hg : ContinuousOn (spectralLiouvilleSlope eta) (Icc a c) :=
    fun t ht => (spectralLiouvilleSlope_hasDerivAt eta t (ht0 t ht)).continuousAt.continuousWithinAt
  have he : ContinuousOn (spectralLiouvilleSecond eta) (Icc a c) := by
    apply continuousOn_const.sub
    apply continuousOn_const.div (continuousOn_id.pow 4)
    exact fun t ht => pow_ne_zero _ (ht0 t ht).ne'
  have hD : ContinuousOn D (Icc a c) := continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hg)
  have hE : ContinuousOn E (Icc a c) := continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn he)
  have hres : ContinuousOn (spectralLiouvilleResidual sign h b eta omega gamma) (Icc a c) := by
    have hc : ContinuousOn (fun t => (5/16 : ℂ)*(D t)^2/(p t)^4-
        E t/(4*(p t)^2)) (Icc a c) :=
      ((continuousOn_const.mul (hD.pow 2)).div (hp.pow 4)
      (fun t ht => pow_ne_zero _ (hpn t ht))).sub
      (hE.div (continuousOn_const.mul (hp.pow 2))
        (fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero _ (hpn t ht))))
    apply hc.congr
    intro t ht
    exact spectralWKB_potential_residual (p t) (D t) (E t) (hpn t ht)
  exact ⟨hres,hres.norm.div hp.norm (fun t ht => norm_ne_zero_iff.mpr (hpn t ht))⟩

end DefocusingNLS

end OAI
