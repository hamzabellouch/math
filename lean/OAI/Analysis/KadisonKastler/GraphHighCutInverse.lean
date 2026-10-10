import OAI.Analysis.KadisonKastler.GraphCutScalarBounds
import OAI.Analysis.KadisonKastler.ModularSpectralCuts

namespace OAI

/-! # A bounded inverse on the high logarithmic cut

The inverse is clipped outside the cut before applying continuous
functional calculus, so it remains a bounded ambient operator.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

private theorem complementScale_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) :
    ContinuousOn (fun s => 1 - s / graphScaleScalar c s) (spectrum ℝ (graphResolvent M J Ω 1)) := by
  apply continuousOn_const.sub
  apply continuousOn_id.div (by unfold graphScaleScalar; fun_prop)
  intro s hs
  have hb := graphResolvent_spectrum_bounds J Ω hs
  exact (graphScaleScalar_pos hc hb.1 hb.2).ne'

theorem one_sub_graphResolvent_eq_cfc_scale (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) :
    1 - graphResolvent M J Ω c =
      cfc (fun s => 1 - s / graphScaleScalar c s) (graphResolvent M J Ω 1) := by
  have hquot : ContinuousOn (fun s : ℝ => s / graphScaleScalar c s)
      (spectrum ℝ (graphResolvent M J Ω 1)) := by
    apply continuousOn_id.div (by unfold graphScaleScalar; fun_prop)
    intro s hs
    have hb := graphResolvent_spectrum_bounds J Ω hs
    exact (graphScaleScalar_pos hc hb.1 hb.2).ne'
  rw [cfc_sub (fun _ : ℝ => 1) (fun s => s / graphScaleScalar c s) _
    continuousOn_const hquot,
    cfc_const_one ℝ _ (graphResolvent_positive J Ω 1).isSelfAdjoint,
    ← graphResolvent_eq_cfc_scale J Ω hc]

def graphHighCutInverse (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (c r : ℝ) : H →L[ℂ] H :=
  cfc (graphHighInverseScalar c r) (graphResolvent M J Ω 1) *
    resolventLowerCut (graphResolvent M J Ω 1) r

theorem graphHighCutInverse_bound (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c r : ℝ} (hc : c ≠ 0) (hr : 0 ≤ r) (hr1 : r < 1) :
    ‖graphHighCutInverse M J Ω c r‖ ≤ graphScaleScalar c r / (c ^ 2 * (1 - r)) := by
  have hk : 0 ≤ graphScaleScalar c r / (c ^ 2 * (1 - r)) := by
    exact div_nonneg (graphScaleScalar_pos hc hr hr1.le).le
      (mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hr1.le))
  have hf : ‖cfc (graphHighInverseScalar c r) (graphResolvent M J Ω 1)‖ ≤
      graphScaleScalar c r / (c ^ 2 * (1 - r)) := by
    apply norm_cfc_le hk
    intro s hs
    have hb := graphResolvent_spectrum_bounds J Ω hs
    rw [Real.norm_eq_abs, abs_of_nonneg (graphHighInverseScalar_nonneg hc hr hr1 hb.1)]
    exact graphHighInverseScalar_bound hc hr hr1 hb.1
  calc
    _ ≤ ‖cfc (graphHighInverseScalar c r) (graphResolvent M J Ω 1)‖ *
        ‖resolventLowerCut (graphResolvent M J Ω 1) r‖ := norm_mul_le _ _
    _ ≤ (graphScaleScalar c r / (c ^ 2 * (1 - r))) * 1 :=
      mul_le_mul hf ((resolventLowerCut_projection _ _).norm_le _) (norm_nonneg _) hk
    _ = _ := mul_one _

theorem graphHighCutInverse_supported (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (c r : ℝ) :
    resolventLowerCut (graphResolvent M J Ω 1) r * graphHighCutInverse M J Ω c r =
      graphHighCutInverse M J Ω c r := by
  have hc := resolventLowerCut_commutes_cfc (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint r (graphHighInverseScalar c r)
  rw [graphHighCutInverse, ← mul_assoc, hc.eq, mul_assoc,
    (resolventLowerCut_projection _ _).isIdempotentElem.eq]

theorem graphHighCutInverse_identity (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c r : ℝ} (hc : c ≠ 0) (hr1 : r < 1) :
    (1 - graphResolvent M J Ω c) * graphHighCutInverse M J Ω c r =
      resolventLowerCut (graphResolvent M J Ω 1) r := by
  let R := graphResolvent M J Ω 1
  let f := graphHighInverseScalar c r
  let g := fun s => 1 - s / graphScaleScalar c s
  have hf : ContinuousOn f (spectrum ℝ R) :=
    (graphHighInverseScalar_continuousOn hc hr1).mono
      (fun s hs => graphResolvent_spectrum_bounds J Ω hs)
  have hg : ContinuousOn g (spectrum ℝ R) := complementScale_continuousOn J Ω hc
  have hz : ((1 - graphResolvent M J Ω c) * cfc f R - 1) * resolventCutGenerator R r = 0 := by
    rw [one_sub_graphResolvent_eq_cfc_scale J Ω hc]
    change (cfc g R * cfc f R - 1) * cfc (fun s : ℝ => max (r - s) 0) R = 0
    rw [← cfc_mul g f R hg hf, ← cfc_const_one ℝ R (graphResolvent_positive J Ω 1).isSelfAdjoint,
      ← cfc_sub (fun s => g s * f s) (fun _ : ℝ => 1) R (hg.mul hf) continuousOn_const,
      ← cfc_mul (fun s => g s * f s - 1) (fun s : ℝ => max (r - s) 0) R
        ((hg.mul hf).sub continuousOn_const) (by fun_prop)]
    calc
      _ = cfc (fun _ : ℝ => 0) R := by
        apply cfc_congr
        intro s hs
        have hb := graphResolvent_spectrum_bounds J Ω hs
        exact graphHighInverseScalar_cut_identity hc hr1 hb.1 hb.2
      _ = 0 := cfc_const_zero ℝ R
  have hp := mul_resolventLowerCut_eq_zero R _ r hz
  rw [sub_mul, one_mul, mul_assoc] at hp
  exact sub_eq_zero.mp hp

end

end KadisonKastler

end OAI
