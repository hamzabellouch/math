import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleReflectedError
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBReflectedCone

namespace OAI

/-! The forbidden Liouville equation satisfies the inner Robin cone
under the turning-coefficient and error criteria. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_reflected_cone (h b eta omega gamma R E : ℝ)
    (hR : 0 < R) (hRE : R ≤ E)
    (hF : ∀ t ∈ Icc R E, 0 < (-1)*homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : ∀ t ∈ Icc R E, |spectralLiouvilleSlope eta t| ≤
      2*‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖^3)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R E))
    (hODE : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t)
    (hN : 0 < spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum (-1) h b eta omega gamma E‖) (q E))
    (ha :
      let p := spectralLiouvilleMomentum (-1) h b eta omega gamma E
      spectralShellNorm (Real.sqrt ‖p‖) (q E)/8 ≤
        ‖spectralScalarWronskian ((Complex.sqrt p)⁻¹,
          (p+(spectralLiouvilleSlope eta E : ℂ)/(4*p^2))*(Complex.sqrt p)⁻¹) (q E)/(-2)‖)
    (herror :
      let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
      let J := ∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/‖p t‖
      let H := (∫ t in R..E, p t).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ 1/64) :
    let p := spectralLiouvilleMomentum (-1) h b eta omega gamma R
    (q R).1 ≠ 0 ∧ ‖(q R).2+(p-(spectralLiouvilleSlope eta R : ℂ)/(4*p^2))*(q R).1‖ ≤
      (1/2 : ℝ)*‖p‖*‖(q R).1‖ := by
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
  have hvform (t : ℝ) : v t/(2*p t) = -(spectralLiouvilleSlope eta t : ℂ)/(4*(p t)^2) := by
    dsimp only [v,D]
    simp only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul]
    ring
  have ha' : spectralShellNorm (k E) (q E)/8 ≤
      ‖spectralScalarWronskian ((Complex.sqrt (p E))⁻¹,
        (p E-v E/(2*p E))*(Complex.sqrt (p E))⁻¹) (q E)/(-2)‖ := by
    rw [hvform]
    simpa only [p,k,neg_div,sub_neg_eq_add] using ha
  have herr :
      let J := ∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2
      let H := (∫ t in R..E, p t).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ 1/64 := by
    dsimp only
    simp only [hk2]
    simpa only [p,v,w,D,B,spectralLiouvilleResidual] using herror
  have hc := spectralWKB_reflected_cone R E hRE p v w q k hp hv hw hq hk hk0
    (fun t _ => hk2 t) (fun t ht => hpD t ⟨ht.1.le,ht.2.le⟩)
    (fun t ht => hvD t ⟨ht.1.le,ht.2.le⟩) hsv
    (fun t _ => spectralComplexSqrt_re_nonneg _) hqD hN ha' herr
  rw [hvform] at hc
  simpa only [p,neg_div,← sub_eq_add_neg] using hc

theorem spectralLiouville_reflected_relative_bounds (eps : ℝ) (heps : 0 < eps) (h b eta omega gamma R E : ℝ)
    (hR : 0 < R) (hRE : R ≤ E)
    (hF : ∀ t ∈ Icc R E, 0 < (-1)*homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : ∀ t ∈ Icc R E, |spectralLiouvilleSlope eta t| ≤
      2*‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖^3)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R E))
    (hODE : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t)
    (hN : 0 < spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum (-1) h b eta omega gamma E‖) (q E))
    (ha :
      let p := spectralLiouvilleMomentum (-1) h b eta omega gamma E
      spectralShellNorm (Real.sqrt ‖p‖) (q E)/8 ≤
        ‖spectralScalarWronskian ((Complex.sqrt p)⁻¹,
          (p+(spectralLiouvilleSlope eta E : ℂ)/(4*p^2))*(Complex.sqrt p)⁻¹) (q E)/(-2)‖)
    (herror :
      let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
      let J := ∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/‖p t‖
      let H := (∫ t in R..E, p t).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ min (1/16) (eps/40)) :
    let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
    ((q R).1 ≠ 0 ∧ ‖(q R).2+(p R-(spectralLiouvilleSlope eta R : ℂ)/(4*(p R)^2))*(q R).1‖ ≤
      eps*‖p R‖*‖(q R).1‖) ∧
      (1/16 : ℝ)*Real.exp ((∫ t in R..E, p t).re)*
        spectralShellNorm (Real.sqrt ‖p E‖) (q E) ≤ Real.sqrt ‖p R‖*‖(q R).1‖ := by
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
  have hvform (t : ℝ) : v t/(2*p t) = -(spectralLiouvilleSlope eta t : ℂ)/(4*(p t)^2) := by
    dsimp only [v,D]
    simp only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul]
    ring
  have ha' : spectralShellNorm (k E) (q E)/8 ≤
      ‖spectralScalarWronskian ((Complex.sqrt (p E))⁻¹,
        (p E-v E/(2*p E))*(Complex.sqrt (p E))⁻¹) (q E)/(-2)‖ := by
    rw [hvform]
    simpa only [p,k,neg_div,sub_neg_eq_add] using ha
  have herr :
      let J := ∫ t in R..E, (25/4 : ℝ)*‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2
      let H := (∫ t in R..E, p t).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ min (1/16) (eps/40) := by
    dsimp only
    simp only [hk2]
    simpa only [p,v,w,D,B,spectralLiouvilleResidual] using herror
  have hc := spectralWKB_reflected_relative_bounds eps heps R E hRE p v w q k hp hv hw hq hk hk0
    (fun t _ => hk2 t) (fun t ht => hpD t ⟨ht.1.le,ht.2.le⟩)
    (fun t ht => hvD t ⟨ht.1.le,ht.2.le⟩) hsv
    (fun t _ => spectralComplexSqrt_re_nonneg _) hqD hN ha' herr
  rw [hvform] at hc
  simpa only [p,neg_div,← sub_eq_add_neg] using hc

theorem spectralLiouville_reflected_relative_cone (eps : ℝ) (heps : 0 < eps) (h b eta omega gamma R E : ℝ)
    (hR : 0 < R) (hRE : R ≤ E)
    (hF : ∀ t ∈ Icc R E, 0 < (-1)*homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : ∀ t ∈ Icc R E, |spectralLiouvilleSlope eta t| ≤
      2*‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖^3)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R E))
    (hODE : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t)
    (hN : 0 < spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum (-1) h b eta omega gamma E‖) (q E))
    (ha :
      let p := spectralLiouvilleMomentum (-1) h b eta omega gamma E
      spectralShellNorm (Real.sqrt ‖p‖) (q E)/8 ≤
        ‖spectralScalarWronskian ((Complex.sqrt p)⁻¹,
          (p+(spectralLiouvilleSlope eta E : ℂ)/(4*p^2))*(Complex.sqrt p)⁻¹) (q E)/(-2)‖)
    (herror :
      let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
      let J := ∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/‖p t‖
      let H := (∫ t in R..E, p t).re
      (25/4 : ℝ)*Real.exp J*J+(25/8)*Real.exp (-2*H) ≤ min (1/16) (eps/40)) :
    let p := spectralLiouvilleMomentum (-1) h b eta omega gamma R
    (q R).1 ≠ 0 ∧ ‖(q R).2+(p-(spectralLiouvilleSlope eta R : ℂ)/(4*p^2))*(q R).1‖ ≤
      eps*‖p‖*‖(q R).1‖ := by
  exact (spectralLiouville_reflected_relative_bounds eps heps h b eta omega gamma R E
    hR hRE hF hsmall q hq hODE hN ha herror).1

end DefocusingNLS

end OAI
