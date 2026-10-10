import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleOutgoingBranch
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBBranchAmplitude
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOscillatoryWeight

namespace OAI

/-! The actual outgoing normalization gives a uniformly positive flux for
the selected comparison branch, before estimating its error. -/

open Set
namespace DefocusingNLS

theorem spectralLiouville_outgoing_branch_margin
    (h b eta omega gamma R E Bnd : ℝ) (hh : h^2 = 1) (hR : 0 < R) (hRE : R ≤ E)
    (hF : ∀ t ∈ Icc R E, 0 < homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : |spectralLiouvilleSlope eta R| ≤
      2*‖spectralLiouvilleMomentum 1 h b eta omega gamma R‖^3)
    (hphase : |(spectralWKBPhase R ((h : ℂ)*Complex.I)
      (spectralLiouvilleMomentum 1 h b eta omega gamma) E).re| ≤ Bnd)
    (hgamma : |gamma| ≤ homogeneousSpectralLocalizationFrequency h b eta omega E) :
    let p := spectralLiouvilleMomentum 1 h b eta omega gamma
    let v := fun t => (spectralLiouvilleSlope eta t : ℂ)/(2*p t)
    let D := spectralWKBFrame R ((h : ℂ)*Complex.I) p v
    let x := spectralOscillatoryData h
      (Real.sqrt (Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega E)))
    let z := x.1/(D E).1
    (Real.exp (-Bnd))^2/6 ≤ h*spectralScalarFlux (z • D R) ∧
      spectralShellNorm (Real.sqrt ‖p R‖) (z • D R) ≤ 5*Real.exp Bnd := by
  dsimp only
  let p := spectralLiouvilleMomentum 1 h b eta omega gamma
  let v := fun t => (spectralLiouvilleSlope eta t : ℂ)/(2*p t)
  let k := fun t => Real.sqrt ‖p t‖
  let chi := (h : ℂ)*Complex.I
  let D := spectralWKBFrame R chi p v
  let x := spectralOscillatoryData h
    (Real.sqrt (Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega E)))
  let z := x.1/(D E).1
  have hRI : R ∈ Icc R E := ⟨le_rfl,hRE⟩
  have hEI : E ∈ Icc R E := ⟨hRE,le_rfl⟩
  have hk (t : ℝ) (ht : t ∈ Icc R E) : 0 < k t := by
    apply Real.sqrt_pos.mpr
    apply lt_of_lt_of_le (Real.sqrt_pos.mpr (hF t ht))
    simpa only [p,spectralLiouvilleMomentum,abs_of_pos (hF t ht)] using
      spectralWKBSqrt_frequency_lower 1 (homogeneousSpectralLocalizationFrequency h b eta omega t)
        gamma (by norm_num)
  have hpn (t : ℝ) (ht : t ∈ Icc R E) : p t ≠ 0 :=
    norm_pos_iff.mp ((Real.sqrt_pos.mp (hk t ht)))
  have hpD (t : ℝ) (ht : t ∈ Icc R E) : HasDerivAt p (v t) t := by
    simpa only [Complex.ofReal_one,one_mul] using
      spectralLiouvilleMomentum_hasDerivAt 1 h b eta omega gamma t (hR.trans_le ht.1)
        (by simpa only [one_mul] using hF t ht)
  have hp : ContinuousOn p (Icc R E) := fun t ht => (hpD t ht).continuousAt.continuousWithinAt
  have hv : ContinuousOn v (Icc R E) := by
    apply (Complex.continuous_ofReal.comp_continuousOn (show ContinuousOn (spectralLiouvilleSlope eta) (Icc R E) from
      fun t ht => (spectralLiouvilleSlope_hasDerivAt eta t (hR.trans_le ht.1)).continuousAt.continuousWithinAt)).div
      (continuousOn_const.mul hp)
    exact fun t ht => mul_ne_zero (by norm_num) (hpn t ht)
  have hkp (t : ℝ) : (k t)^2 = ‖p t‖ := Real.sq_sqrt (norm_nonneg _)
  have hchi : ‖chi‖ = 1 := by
    have hhabs : |h| = 1 := by nlinarith [sq_abs h,abs_nonneg h]
    simp only [chi,norm_mul,Complex.norm_real,Real.norm_eq_abs,hhabs,Complex.norm_I,mul_one]
  have hvs : ‖v R‖ ≤ ‖p R‖^2 := by
    have hnp : 0 < ‖p R‖ := norm_pos_iff.mpr (hpn R hRI)
    dsimp only [v]
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    norm_num only [Complex.norm_ofNat]
    apply (div_le_iff₀ (by positivity : 0 < 2*‖p R‖)).mpr
    nlinarith
  have hEpos := hF E hEI
  have hkr : 0 < Real.sqrt (Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega E)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hEpos)
  have hweights := spectralComplexSqrt_weight_comparable
    (homogeneousSpectralLocalizationFrequency h b eta omega E) gamma hEpos hgamma
  have hxnorm : ‖x.1‖ = (Real.sqrt (Real.sqrt
      (homogeneousSpectralLocalizationFrequency h b eta omega E)))⁻¹ := by
    simp only [x,spectralOscillatoryData,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hkr]
  have hxl : 1 ≤ k E*‖x.1‖ := by
    rw [hxnorm,← div_eq_mul_inv]
    apply (le_div_iff₀ hkr).mpr
    simpa only [p,spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,one_mul,k,one_mul] using hweights.1
  have hxu : k E*‖x.1‖ ≤ 2 := by
    rw [hxnorm,← div_eq_mul_inv]
    apply (div_le_iff₀ hkr).mpr
    simpa only [p,spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,one_mul,k] using hweights.2
  obtain ⟨hzlo,_,hzb⟩ := spectralWKB_branch_amplitude R E Bnd (k R) (k E) hRE chi hchi p v hp hv hpn
    (fun t ht => hpD t ⟨ht.1.le,ht.2.le⟩) (hk R hRI) (hk E hEI) (hkp R) (hkp E)
    hvs hphase x.1 hxl hxu
  have hbase : (1/6 : ℝ) ≤ h*spectralScalarFlux (D R) := by
    dsimp only [D]
    rw [spectralWKBFrame_initial]
    simpa only [p,spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,one_mul,chi] using
      spectralWKB_initial_flux_lower h (homogeneousSpectralLocalizationFrequency h b eta omega R) gamma
        (k R) (v R) hh (hF R hRI) (hk R hRI)
        (by simpa only [p,spectralLiouvilleMomentum,spectralWKBSquaredMomentum,
          Complex.ofReal_one,one_mul] using hkp R)
        (by simpa only [p,spectralLiouvilleMomentum,spectralWKBSquaredMomentum,
          Complex.ofReal_one,one_mul] using hvs)
  refine ⟨?_,hzb⟩
  rw [spectralScalarFlux_smul]
  have hzsq : (Real.exp (-Bnd))^2 ≤ ‖z‖^2 := by nlinarith [Real.exp_pos (-Bnd),norm_nonneg z]
  have hm := mul_le_mul_of_nonneg_left hbase (sq_nonneg ‖z‖)
  nlinarith

end DefocusingNLS

end OAI
