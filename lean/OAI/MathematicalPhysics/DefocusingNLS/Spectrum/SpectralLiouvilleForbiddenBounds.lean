import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleForbiddenTransfer

namespace OAI

/-! A single residual integral controls transfer from either endpoint at
every point of the forbidden interval, with the action kept in that channel. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_forbidden_bounds (h b eta omega gamma R E : ℝ)
    (hR : 0 < R) (hRE : R ≤ E)
    (hF : ∀ t ∈ Icc R E, 0 < (-1)*homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : ∀ t ∈ Icc R E, |spectralLiouvilleSlope eta t| ≤
      2*‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖^3)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R E))
    (hODE : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t) :
    let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
    let k := fun t => Real.sqrt ‖p t‖
    let J := ∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/‖p t‖
    let H := fun r => (∫ t in r..E, p t).re
    ∀ r ∈ Icc R E,
      spectralShellNorm (k r) (q r) ≤ (25/4 : ℝ)*Real.exp J*Real.exp (H R-H r)*
        spectralShellNorm (k R) (q R) ∧
      spectralShellNorm (k r) (q r) ≤ (25/2 : ℝ)*Real.exp J*Real.exp (H r)*
        spectralShellNorm (k E) (q E) := by
  dsimp only
  let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
  let k := fun t => Real.sqrt ‖p t‖
  let f := fun t => (25/4 : ℝ)*‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/‖p t‖
  let J := ∫ t in R..E, f t
  let H := fun r => (∫ t in r..E, p t).re
  have hNR : 0 ≤ spectralShellNorm (k R) (q R) :=
    spectralShellNorm_nonneg _ (Real.sqrt_nonneg _) _
  have hNE : 0 ≤ spectralShellNorm (k E) (q E) :=
    spectralShellNorm_nonneg _ (Real.sqrt_nonneg _) _
  have hfc : ContinuousOn f (Icc R E) := by
    have hc := (spectralLiouvilleResidual_continuousOn (-1) h b eta omega gamma R E
      (by norm_num) hR hF).2.const_mul (25/4 : ℝ)
    convert hc using 1
    funext t
    dsimp only [f,p]
    ring
  have hfi : IntervalIntegrable f volume R E := hfc.intervalIntegrable_of_Icc hRE
  have hf0 : ∀ t, 0 ≤ f t := by intro t; dsimp only [f]; positivity
  have hpc : ContinuousOn p (Icc R E) := fun t ht =>
    (spectralLiouvilleMomentum_hasDerivAt (-1) h b eta omega gamma t
      (hR.trans_le ht.1) (hF t ht)).continuousAt.continuousWithinAt
  intro r hr
  have hL : Icc R r ⊆ Icc R E := Icc_subset_Icc le_rfl hr.2
  have hT : Icc r E ⊆ Icc R E := Icc_subset_Icc hr.1 le_rfl
  have hJL : (∫ t in R..r, f t) ≤ J :=
    intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2 (Filter.Eventually.of_forall hf0) hfi
  have hJT : (∫ t in r..E, f t) ≤ J :=
    intervalIntegral.integral_mono_interval hr.1 hr.2 le_rfl (Filter.Eventually.of_forall hf0) hfi
  have ha : (∫ t in R..r, p t).re = H R-H r := by
    have hiL : IntervalIntegrable p volume R r := (hpc.mono hL).intervalIntegrable_of_Icc hr.1
    have hiT : IntervalIntegrable p volume r E := (hpc.mono hT).intervalIntegrable_of_Icc hr.2
    have he := congrArg Complex.re (intervalIntegral.integral_add_adjacent_intervals
      hiL hiT)
    simp only [Complex.add_re] at he
    dsimp only [H]
    linear_combination he
  have hleft := (spectralLiouville_forbidden_endpoint h b eta omega gamma R r hR hr.1
    (fun t ht => hF t (hL ht)) (fun t ht => hsmall t (hL ht)) q (hq.mono hL)
    (fun t ht => hODE t ⟨ht.1,ht.2.trans_le hr.2⟩)).1
  have hright := (spectralLiouville_forbidden_endpoint h b eta omega gamma r E
    (hR.trans_le hr.1) hr.2 (fun t ht => hF t (hT ht)) (fun t ht => hsmall t (hT ht))
    q (hq.mono hT) (fun t ht => hODE t ⟨hr.1.trans_lt ht.1,ht.2⟩)).2
  dsimp only at hleft hright
  change spectralShellNorm (k r) (q r) ≤ (25/4 : ℝ)*Real.exp ((∫ t in R..r, p t).re+
    ∫ t in R..r, f t)*spectralShellNorm (k R) (q R) at hleft
  change spectralShellNorm (k r) (q r) ≤ (2*((25/4 : ℝ)*Real.exp (H r+
    ∫ t in r..E, f t)))*spectralShellNorm (k E) (q E) at hright
  rw [ha] at hleft
  constructor
  · calc
      _ ≤ (25/4 : ℝ)*Real.exp (H R-H r+J)*spectralShellNorm (k R) (q R) :=
        hleft.trans (by gcongr)
      _ = _ := by rw [Real.exp_add]; ring
  · calc
      _ ≤ (2*((25/4 : ℝ)*Real.exp (H r+J)))*spectralShellNorm (k E) (q E) :=
        hright.trans (by gcongr)
      _ = _ := by rw [Real.exp_add]; ring

end DefocusingNLS

end OAI
