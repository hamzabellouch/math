import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBReflectedError

namespace OAI

/-! Forbidden-side Liouville transport error from the turning edge
back to the fixed inner radius, with the momentum jets computed explicitly. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_reflected_error (h b eta omega gamma R E : ℝ)
    (hR : 0 < R) (hRE : R ≤ E)
    (hF : ∀ t ∈ Icc R E, 0 < (-1)*homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : ∀ t ∈ Icc R E, |spectralLiouvilleSlope eta t| ≤
      2*‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖^3)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R E))
    (hODE : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t) :
    let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
    let P := fun t => p (R+E-t)
    let v := fun t => -((-1 : ℂ)*(spectralLiouvilleSlope eta (R+E-t) : ℂ)/(2*P t))
    let Q := spectralScalarReflect R E q
    let D := spectralWKBFrame R 1 P v
    let U := spectralWKBFrame R (-1) P v
    let J := ∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/‖p t‖
    spectralShellNorm (Real.sqrt ‖p R‖)
      (Q E-((spectralScalarWronskian (Q R) (U R)/(-2)) • D E+
        (spectralScalarWronskian (D R) (Q R)/(-2)) • U E)) ≤
      ((25/4 : ℝ)*spectralShellNorm (Real.sqrt ‖p E‖) (q E))*
        Real.exp ((∫ t in R..E, p t).re+J)*J := by
  dsimp only
  have hs : (-1 : ℝ)^2 = 1 := by norm_num
  let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
  let D := fun t => (((-1 : ℝ) : ℂ))*(spectralLiouvilleSlope eta t : ℂ)
  let B := fun t => (((-1 : ℝ) : ℂ))*(spectralLiouvilleSecond eta t : ℂ)
  let v := fun t => D t/(2*p t)
  let w := fun t => B t/(2*p t)-(D t)^2/(4*(p t)^3)
  let k := fun t => Real.sqrt ‖p t‖
  have ht0 (t : ℝ) (ht : t ∈ Icc R E) : 0<t := hR.trans_le ht.1
  have hpD (t : ℝ) (ht : t ∈ Icc R E) : HasDerivAt p (v t) t :=
    spectralLiouvilleMomentum_hasDerivAt (-1) h b eta omega gamma t (ht0 t ht) (hF t ht)
  have hvD (t : ℝ) (ht : t ∈ Icc R E) : HasDerivAt v (w t) t :=
    spectralLiouvilleMomentumSlope_hasDerivAt (-1) h b eta omega gamma t (ht0 t ht) (hF t ht)
  have hp : ContinuousOn p (Icc R E) := fun t ht => (hpD t ht).continuousAt.continuousWithinAt
  have hv : ContinuousOn v (Icc R E) := fun t ht => (hvD t ht).continuousAt.continuousWithinAt
  have hpn (t : ℝ) (ht : t ∈ Icc R E) : p t≠0 := by
    have hf : homogeneousSpectralLocalizationFrequency h b eta omega t≠0 := by
      intro he
      have hh := hF t ht
      rw [he,mul_zero] at hh
      exact lt_irrefl _ hh
    have hk := spectralWKBSqrt_frequency_lower (-1)
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
  have hsign : |(-1 : ℝ)|=1 := by norm_num
  have hsv (t : ℝ) (ht : t ∈ Icc R E) : ‖v t‖≤‖p t‖^2 := by
    have hpos : 0<‖p t‖ := norm_pos_iff.mpr (hpn t ht)
    dsimp only [v,D]
    simp only [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,hsign,
      one_mul,Complex.norm_ofNat]
    apply (div_le_iff₀ (by positivity : 0<2*‖p t‖)).mpr
    nlinarith [hsmall t ht]
  have hqD (t : ℝ) (ht : t ∈ Ioo R E) :
      HasDerivAt q (spectralScalarField (-(p t)^2) (q t)) t := by
    have hsq : (p t)^2 = (-1 : ℂ)*
        ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ)) :=
      by simpa only [p,spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_neg,Complex.ofReal_one] using
        spectralComplexSqrt_sq (spectralWKBSquaredMomentum (-1)
          (homogeneousSpectralLocalizationFrequency h b eta omega t) gamma)
    have he : -(p t)^2 =
        (homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ) := by
      rw [hsq]
      ring
    rw [he]
    exact hODE t ht
  have hh := spectralWKB_reflected_action_error R E hRE p v w q k hp hv hw hq hk hk0
    (fun t _ => hk2 t) (fun t ht => hpD t ⟨ht.1.le,ht.2.le⟩)
    (fun t ht => hvD t ⟨ht.1.le,ht.2.le⟩) hsv
    (fun t _ => spectralComplexSqrt_re_nonneg _) hqD
  dsimp only at hh
  rw [spectralWKB_reflected_residual_integral,spectralWKB_reflected_phase] at hh
  simp only [hk2] at hh
  simpa only [p,v,w,D,B,k,spectralLiouvilleResidual,Complex.ofReal_neg,Complex.ofReal_one] using hh

end DefocusingNLS

end OAI
