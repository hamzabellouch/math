import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleForbiddenBounds
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGreenScaledFrame

namespace OAI

/-! The actual forbidden scalar equation has a Dirichlet/outgoing Green
kernel with a uniform bound. The arbitrary outgoing normalization cancels. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_forbidden_green_data (h b eta omega gamma R E : ℝ)
    (hR : 0 < R) (hRE : R ≤ E)
    (hF : ∀ t ∈ Icc R E, 0 < (-1)*homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : ∀ t ∈ Icc R E, |spectralLiouvilleSlope eta t| ≤
      2*‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖^3)
    (U : ℝ → ℂ × ℂ) (hUc : ContinuousOn U (Icc R E))
    (hUD : ∀ t ∈ Icc R E, HasDerivAt U
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (U t)) t)
    (hN : 0 < spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum (-1) h b eta omega gamma E‖) (U E))
    (hvalue :
      let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
      (1/16 : ℝ)*Real.exp ((∫ t in R..E, p t).re)*
        spectralShellNorm (Real.sqrt ‖p E‖) (U E) ≤ Real.sqrt ‖p R‖*‖(U R).1‖) :
    let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
    let k := fun t => Real.sqrt ‖p t‖
    let J := ∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/‖p t‖
    ∃ (D : ℝ → ℂ × ℂ) (W : ℂ), Continuous D ∧ D R = (0,(k R : ℂ)) ∧
      (∀ t ∈ Icc R E, HasDerivAt D (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ)) (D t)) t) ∧
      W ≠ 0 ∧ (∀ t ∈ Icc R E, spectralScalarWronskian (D t) (U t) = W) ∧
      ∀ r ∈ Icc R E, ∀ t ∈ Icc R E,
        spectralShellNorm (k r) (spectralScalarGreenState D U W r t) ≤ 1250*Real.exp (2*J)/(k t) := by
  dsimp only
  let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
  let k := fun t => Real.sqrt ‖p t‖
  let V := fun t => (homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ)
  let J := ∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/‖p t‖
  let H := fun r => (∫ t in r..E, p t).re
  let N := spectralShellNorm (k E) (U E)
  let A := (25/4 : ℝ)*Real.exp J
  let B := (25/2 : ℝ)*Real.exp J
  have hkp (t : ℝ) (ht : t ∈ Icc R E) : 0 < k t :=
    spectralLiouville_norm_weight_pos (-1) h b eta omega gamma t (by norm_num)
      (by intro he; have hf := hF t ht; rw [he,mul_zero] at hf; linarith)
  have hpc : ContinuousOn p (Icc R E) := fun t ht =>
    (spectralLiouvilleMomentum_hasDerivAt (-1) h b eta omega gamma t
      (hR.trans_le ht.1) (hF t ht)).continuousAt.continuousWithinAt
  have hV : ContinuousOn V (Icc R E) :=
    (Complex.continuous_ofReal.comp_continuousOn (fun t ht =>
      (homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t
        (hR.trans_le ht.1)).continuousAt.continuousWithinAt)).add continuousOn_const
  obtain ⟨D,hDc,hDR,hDD⟩ := spectralScalar_local_exists R E hRE V hV (0,(k R : ℂ))
  have hDN : spectralShellNorm (k R) (D R) = 1 := by
    rw [hDR]
    simp only [spectralShellNorm,norm_zero,mul_zero,zero_add,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (hkp R ⟨le_rfl,hRE⟩),inv_mul_cancel₀ (hkp R ⟨le_rfl,hRE⟩).ne']
  have hDb (r : ℝ) (hr : r ∈ Icc R E) :
      spectralShellNorm (k r) (D r) ≤ A*Real.exp (H R-H r) := by
    have hh := (spectralLiouville_forbidden_bounds h b eta omega gamma R E hR hRE hF hsmall D
      hDc.continuousOn (fun t ht => hDD t ⟨ht.1.le,ht.2.le⟩) r hr).1
    change spectralShellNorm (k r) (D r) ≤ A*Real.exp (H R-H r)*spectralShellNorm (k R) (D R) at hh
    simpa only [hDN,mul_one] using hh
  have hUb (r : ℝ) (hr : r ∈ Icc R E) :
      spectralShellNorm (k r) (U r) ≤ B*N*Real.exp (H r) := by
    have hh := (spectralLiouville_forbidden_bounds h b eta omega gamma R E hR hRE hF hsmall U
      hUc (fun t ht => hUD t ⟨ht.1.le,ht.2.le⟩) r hr).2
    convert hh using 1
    dsimp only [B,N]
    ring
  let W := spectralScalarWronskian (D R) (U R)
  have hWnorm : ‖W‖ = k R*‖(U R).1‖ := by
    simp only [W,hDR,spectralScalarWronskian,zero_mul,zero_sub,norm_neg,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hkp R ⟨le_rfl,hRE⟩)]
  have hW : (1/16 : ℝ)*N*Real.exp (H R) ≤ ‖W‖ := by
    rw [hWnorm]
    convert hvalue using 1
    ring
  have hW0 : W ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hW)
  have hdet (r : ℝ) (hr : r ∈ Icc R E) : spectralScalarWronskian (D r) (U r) = W :=
    spectralScalarWronskian_eq R r hr.1 V D U
      (hDc.continuousOn.mono (Icc_subset_Icc le_rfl hr.2))
      (hUc.mono (Icc_subset_Icc le_rfl hr.2))
      (fun t ht => hDD t ⟨ht.1.le,ht.2.le.trans hr.2⟩)
      (fun t ht => hUD t ⟨ht.1.le,ht.2.le.trans hr.2⟩)
  have hH : AntitoneOn H (Icc R E) := by
    intro r hr s hs hrs
    have hi₁ : IntervalIntegrable p volume r s :=
      (hpc.mono (Icc_subset_Icc hr.1 hs.2)).intervalIntegrable_of_Icc hrs
    have hi₂ : IntervalIntegrable p volume s E :=
      (hpc.mono (Icc_subset_Icc hs.1 le_rfl)).intervalIntegrable_of_Icc hs.2
    have he := congrArg Complex.re (intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂)
    have hn : 0 ≤ (∫ t in r..s, p t).re := by
      have heRe : (∫ t in r..s, p t).re = ∫ t in r..s, (p t).re :=
        (intervalIntegral.intervalIntegral_re hi₁).symm
      rw [heRe]
      exact intervalIntegral.integral_nonneg hrs (fun t _ => spectralComplexSqrt_re_nonneg _)
    simp only [Complex.add_re] at he
    change (∫ t in s..E, p t).re ≤ (∫ t in r..E, p t).re
    linarith
  refine ⟨D,W,hDc,hDR,hDD,hW0,hdet,?_⟩
  intro r hr t ht
  have hb := spectralScalarGreenState_scaled_bound D U W k H A B (1/16) N (H R) r t
    (by dsimp only [A]; positivity) (by dsimp only [B]; positivity) (by norm_num) hN
    (hkp r hr) (hkp t ht)
    (fun s hs => by
      rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hs : s = r ∨ s = t) with rfl | rfl
      · exact hDb _ hr
      · exact hDb _ ht)
    (fun s hs => by
      rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hs : s = r ∨ s = t) with rfl | rfl
      · exact hUb _ hr
      · exact hUb _ ht) hW
    (hH.mono (fun s hs => ⟨(le_min hr.1 ht.1).trans hs.1,hs.2.trans (max_le hr.2 ht.2)⟩))
  apply hb.trans_eq
  dsimp only [A,B]
  rw [show 2*J = J+J by ring,Real.exp_add]
  ring

end DefocusingNLS

end OAI
