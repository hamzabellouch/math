import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleResidualContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBPhaseOrder

namespace OAI

/-! Apply the constructed WKB frame to the actual Liouville equation. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_transfer (sign h b eta omega gamma R E : ℝ)
    (hs : sign^2=1) (hR : 0<R) (hRE : R≤E) (chi : ℂ) (hchi : ‖chi‖=1)
    (hchi2 : chi^2*(sign : ℂ)=-1)
    (hF : ∀ t ∈ Icc R E, 0<sign*homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : ∀ t ∈ Icc R E, |spectralLiouvilleSlope eta t|≤
      2*‖spectralLiouvilleMomentum sign h b eta omega gamma t‖^3)
    (hphase : ∀ t ∈ Ioo R E, 0≤(chi*spectralLiouvilleMomentum sign h b eta omega gamma t).re)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R E))
    (hODE : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t) :
    ∀ r ∈ Icc R E,
      spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum sign h b eta omega gamma r‖) (q r)≤
      (25/4 : ℝ)*spectralShellNorm
        (Real.sqrt ‖spectralLiouvilleMomentum sign h b eta omega gamma R‖) (q R)*
      Real.exp ((spectralWKBPhase R chi (spectralLiouvilleMomentum sign h b eta omega gamma) r).re-
        (spectralWKBPhase R chi (spectralLiouvilleMomentum sign h b eta omega gamma) R).re+
        ∫ t in R..r, (25/4 : ℝ)*‖spectralLiouvilleResidual sign h b eta omega gamma t‖/
          ‖spectralLiouvilleMomentum sign h b eta omega gamma t‖) := by
  let p := spectralLiouvilleMomentum sign h b eta omega gamma
  let D := fun t => (sign : ℂ)*(spectralLiouvilleSlope eta t : ℂ)
  let B := fun t => (sign : ℂ)*(spectralLiouvilleSecond eta t : ℂ)
  let v := fun t => D t/(2*p t)
  let w := fun t => B t/(2*p t)-(D t)^2/(4*(p t)^3)
  let k := fun t => Real.sqrt ‖p t‖
  have ht0 (t : ℝ) (ht : t ∈ Icc R E) : 0<t := hR.trans_le ht.1
  have hpD (t : ℝ) (ht : t ∈ Icc R E) : HasDerivAt p (v t) t :=
    spectralLiouvilleMomentum_hasDerivAt sign h b eta omega gamma t (ht0 t ht) (hF t ht)
  have hvD (t : ℝ) (ht : t ∈ Icc R E) : HasDerivAt v (w t) t :=
    spectralLiouvilleMomentumSlope_hasDerivAt sign h b eta omega gamma t (ht0 t ht) (hF t ht)
  have hp : ContinuousOn p (Icc R E) := fun t ht => (hpD t ht).continuousAt.continuousWithinAt
  have hv : ContinuousOn v (Icc R E) := fun t ht => (hvD t ht).continuousAt.continuousWithinAt
  have hpn (t : ℝ) (ht : t ∈ Icc R E) : p t≠0 := by
    have hf : homogeneousSpectralLocalizationFrequency h b eta omega t≠0 := by
      intro he
      have hh := hF t ht
      rw [he,mul_zero] at hh
      exact lt_irrefl _ hh
    have hk := spectralWKBSqrt_frequency_lower sign
      (homogeneousSpectralLocalizationFrequency h b eta omega t) gamma hs
    exact norm_pos_iff.mp ((Real.sqrt_pos.2 (abs_pos.2 hf)).trans_le hk)
  have hg : ContinuousOn (spectralLiouvilleSlope eta) (Icc R E) := fun t ht =>
    (spectralLiouvilleSlope_hasDerivAt eta t (ht0 t ht)).continuousAt.continuousWithinAt
  have hb : ContinuousOn (spectralLiouvilleSecond eta) (Icc R E) := by
    apply continuousOn_const.sub
    apply continuousOn_const.div (continuousOn_id.pow 4)
    exact fun t ht => pow_ne_zero _ (ht0 t ht).ne'
  have hD : ContinuousOn D (Icc R E) := continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hg)
  have hB : ContinuousOn B (Icc R E) := continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hb)
  have hw : ContinuousOn w (Icc R E) :=
    (hB.div (continuousOn_const.mul hp) (fun t ht => mul_ne_zero (by norm_num) (hpn t ht))).sub
      ((hD.pow 2).div (continuousOn_const.mul (hp.pow 3))
        (fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero _ (hpn t ht))))
  have hk : ContinuousOn k (Icc R E) := Real.continuous_sqrt.comp_continuousOn hp.norm
  have hk0 (t : ℝ) (ht : t ∈ Icc R E) : 0<k t := Real.sqrt_pos.2 (norm_pos_iff.mpr (hpn t ht))
  have hk2 (t : ℝ) : (k t)^2=‖p t‖ := Real.sq_sqrt (norm_nonneg _)
  have hsign : |sign|=1 := by nlinarith [sq_abs sign,abs_nonneg sign]
  have hsv (t : ℝ) (ht : t ∈ Icc R E) : ‖v t‖≤‖p t‖^2 := by
    have hpos : 0<‖p t‖ := norm_pos_iff.mpr (hpn t ht)
    dsimp only [v,D]
    simp only [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,hsign,
      one_mul,Complex.norm_ofNat]
    apply (div_le_iff₀ (by positivity : 0<2*‖p t‖)).mpr
    nlinarith [hsmall t ht]
  have hqD (t : ℝ) (ht : t ∈ Ioo R E) :
      HasDerivAt q (spectralScalarField (-chi^2*(p t)^2) (q t)) t := by
    have hsq : (p t)^2=(sign : ℂ)*
        ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ)) :=
      spectralComplexSqrt_sq _
    have he : -chi^2*(p t)^2=
        (homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ) := by
      rw [hsq]
      calc
        _ = -(chi^2*(sign : ℂ))*
            ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ)) := by ring
        _ = _ := by rw [hchi2]; ring
    rw [he]
    exact hODE t ht
  have hh := spectralWKB_actual_transfer R E hRE chi hchi p v w q k hp hv hw hq hk hk0
    (fun t _ => hk2 t) (fun t ht => hpD t ⟨ht.1.le,ht.2.le⟩)
    (fun t ht => hvD t ⟨ht.1.le,ht.2.le⟩) hsv
    (spectralWKBPhase_monotone R E hRE chi p hp hphase) hqD
  intro r hr
  have hresult := hh r hr
  simp only [hk2] at hresult
  exact hresult

end DefocusingNLS

end OAI
