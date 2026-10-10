import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleTerminalError
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBSingleBranch
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOscillatoryMismatch

namespace OAI

/-! Compare the actual radial scalar solution with its selected WKB branch.
The terminal mismatch is derived from the prescribed outgoing data. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_outgoing_branch_error
    (h b eta omega gamma R E Bnd J : ℝ) (hh : h^2 = 1)
    (hR : 0 < R) (hRE : R ≤ E) (hE : 0 < E)
    (hF : ∀ t ∈ Icc R E, 0 < 1*homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : ∀ t ∈ Icc R E, |spectralLiouvilleSlope eta t| ≤
      2*‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖^3)
    (hphase : ∀ t ∈ Icc R E,
      |(spectralWKBPhase R ((h : ℂ)*Complex.I) (spectralLiouvilleMomentum 1 h b eta omega gamma) t).re| ≤ Bnd)
    (hJ : (∫ t in R..E, ‖spectralLiouvilleResidual 1 h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖) ≤ J)
    (hFar : E^2/32 ≤ homogeneousSpectralLocalizationFrequency h b eta omega E)
    (hgFar : |spectralLiouvilleSlope eta E| ≤
      4*homogeneousSpectralLocalizationFrequency h b eta omega E/E)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R E))
    (hqE : q E = spectralOscillatoryData h
      (Real.sqrt (Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega E))))
    (hODE : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t) :
    let p := spectralLiouvilleMomentum 1 h b eta omega gamma
    let v := fun t => (spectralLiouvilleSlope eta t : ℂ)/(2*p t)
    let D := spectralWKBFrame R ((h : ℂ)*Complex.I) p v
    let C := (5/2 : ℝ)*Real.exp Bnd
    spectralShellNorm (Real.sqrt ‖p R‖) (q R - ((q E).1/(D E).1) • D R) ≤
      (2*(C^2)^2*Real.exp (C^2*J)*J)*spectralShellNorm (Real.sqrt ‖p E‖) (q E) +
        C^2*((32*|gamma|+8)/E^2) := by
  dsimp only
  have hs : (1 : ℝ)^2 = 1 := by norm_num
  let chi := (h : ℂ)*Complex.I
  have hchi : ‖chi‖ = 1 := by
    have habs : |h| = 1 := by nlinarith [sq_abs h,abs_nonneg h]
    simp only [chi,norm_mul,Complex.norm_real,Real.norm_eq_abs,habs,Complex.norm_I,mul_one]
  have hchi2 : chi^2*(1 : ℂ) = -1 := by
    have hhC : (h : ℂ)^2 = 1 := by exact_mod_cast hh
    simp only [chi,mul_pow,hhC,Complex.I_sq,one_mul,mul_one]
  let p := spectralLiouvilleMomentum 1 h b eta omega gamma
  let D := fun t => (1 : ℂ)*(spectralLiouvilleSlope eta t : ℂ)
  let B := fun t => (1 : ℂ)*(spectralLiouvilleSecond eta t : ℂ)
  let v := fun t => D t/(2*p t)
  let w := fun t => B t/(2*p t)-(D t)^2/(4*(p t)^3)
  let k := fun t => Real.sqrt ‖p t‖
  have ht0 (t : ℝ) (ht : t ∈ Icc R E) : 0<t := hR.trans_le ht.1
  have hpD (t : ℝ) (ht : t ∈ Icc R E) : HasDerivAt p (v t) t :=
    spectralLiouvilleMomentum_hasDerivAt 1 h b eta omega gamma t (ht0 t ht) (hF t ht)
  have hvD (t : ℝ) (ht : t ∈ Icc R E) : HasDerivAt v (w t) t :=
    spectralLiouvilleMomentumSlope_hasDerivAt 1 h b eta omega gamma t (ht0 t ht) (hF t ht)
  have hp : ContinuousOn p (Icc R E) := fun t ht => (hpD t ht).continuousAt.continuousWithinAt
  have hv : ContinuousOn v (Icc R E) := fun t ht => (hvD t ht).continuousAt.continuousWithinAt
  have hpn (t : ℝ) (ht : t ∈ Icc R E) : p t≠0 := by
    have hf : homogeneousSpectralLocalizationFrequency h b eta omega t≠0 := by
      intro he
      have hh := hF t ht
      rw [he,mul_zero] at hh
      exact lt_irrefl _ hh
    have hk := spectralWKBSqrt_frequency_lower 1
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
  have hsv (t : ℝ) (ht : t ∈ Icc R E) : ‖v t‖≤‖p t‖^2 := by
    have hpos : 0<‖p t‖ := norm_pos_iff.mpr (hpn t ht)
    dsimp only [v,D]
    simp only [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      one_mul,Complex.norm_ofNat]
    apply (div_le_iff₀ (by positivity : 0<2*‖p t‖)).mpr
    nlinarith [hsmall t ht]
  have hqD (t : ℝ) (ht : t ∈ Ioo R E) :
      HasDerivAt q (spectralScalarField (-chi^2*(p t)^2) (q t)) t := by
    have hsq : (p t)^2=(1 : ℂ)*
        ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ)) :=
      spectralComplexSqrt_sq _
    have he : -chi^2*(p t)^2=
        (homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ) := by
      rw [hsq]
      calc
        _ = -(chi^2*(1 : ℂ))*
            ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ)) := by ring
        _ = _ := by rw [hchi2]; ring
    rw [he]
    exact hODE t ht
  let Q := spectralWKBFrame R chi p v
  have hKE : 0 < k E := hk0 E ⟨hRE,le_rfl⟩
  have hQE := spectralWKBFrame_value_norm R E hRE chi p v hp hv hpn
    (fun t ht => hpD t ⟨ht.1.le,ht.2.le⟩) (k E) E hKE (hk2 E) ⟨hRE,le_rfl⟩
  have hQnonzero : (Q E).1 ≠ 0 := by
    intro hz
    change k E*‖(Q E).1‖ = _ at hQE
    rw [hz,norm_zero,mul_zero] at hQE
    exact (Real.exp_ne_zero _ hQE.symm)
  have hFE : 0 < homogeneousSpectralLocalizationFrequency h b eta omega E := by
    simpa only [one_mul] using hF E ⟨hRE,le_rfl⟩
  have hKlower : Real.sqrt (Real.sqrt
      (homogeneousSpectralLocalizationFrequency h b eta omega E)) ≤ k E := by
    have hh := Real.sqrt_le_sqrt (spectralWKBSqrt_frequency_lower 1
      (homogeneousSpectralLocalizationFrequency h b eta omega E) gamma (by norm_num))
    simpa only [k,p,spectralLiouvilleMomentum,abs_of_pos hFE] using hh
  have hQrel : (Q E).2 = (homogeneousSpectralWKBLog chi (p E) (v E))*(Q E).1 := rfl
  have hmis := spectralOscillatoryData_mismatch_bound h
    (homogeneousSpectralLocalizationFrequency h b eta omega E) (k E)
    (homogeneousSpectralWKBLog chi (p E) (v E)) (Q E) hFE hKlower hQnonzero hQrel
  have hrem := spectralWKB_remote_mismatch h
    (homogeneousSpectralLocalizationFrequency h b eta omega E) gamma
    (spectralLiouvilleSlope eta E) E hh hE hFar hgFar
  have hend : spectralShellNorm (k E) (q E - ((q E).1/(Q E).1) • Q E) ≤
      (32*|gamma|+8)/E^2 := by
    rw [hqE]
    apply hmis.trans
    simpa only [chi,p,v,D,spectralLiouvilleMomentum,spectralWKBSquaredMomentum,
      Complex.ofReal_one,one_mul] using hrem
  have hJ' : (∫ t in R..E, ‖homogeneousSpectralWKBResidual (p t) (v t) (w t)‖/(k t)^2) ≤ J := by
    simpa only [hk2,p,v,w,D,B,spectralLiouvilleResidual,Complex.ofReal_one,one_mul] using hJ
  have he := spectralWKB_single_branch_error R E Bnd J ((32*|gamma|+8)/E^2) hRE chi hchi
    p v w q k hp hv hw hq hk hk0 (fun t _ => hk2 t)
    (fun t ht => hpD t ⟨ht.1.le,ht.2.le⟩) (fun t ht => hvD t ⟨ht.1.le,ht.2.le⟩)
    hsv hphase hJ' hqD hend
  simpa only [k,p,v,D,chi,Complex.ofReal_one,one_mul] using he

end DefocusingNLS

end OAI
