import OAI.Analysis.KadisonKastler.GraphHighCutInverse
import OAI.Analysis.KadisonKastler.GraphLowCutScalars

namespace OAI

/-! # The complementary low-cut estimate

Clipping the decreasing resolvent complement at the cut changes it by a
multiple of the cut generator. This difference vanishes on the low cut.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem graphComplementScalar_continuousOn (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) :
    ContinuousOn (graphComplementScalar c) (spectrum ℝ (graphResolvent M J Ω 1)) := by
  apply continuousOn_const.sub
  apply continuousOn_id.div (by unfold graphScaleScalar; fun_prop)
  intro s hs
  have hb := graphResolvent_spectrum_bounds J Ω hs
  exact (graphScaleScalar_pos hc hb.1 hb.2).ne'

theorem resolventCutGenerator_mul_complement (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (r : ℝ) :
    resolventCutGenerator R r * (1 - resolventLowerCut R r) = 0 := by
  have hc := resolventLowerCut_commutes_cfc R hR r (fun s : ℝ => max (r - s) 0)
  change Commute (resolventLowerCut R r) (resolventCutGenerator R r) at hc
  rw [mul_sub, mul_one, ← hc.eq, resolventLowerCut_mul_generator, sub_self]

theorem graphLowCut_clipped (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c r : ℝ} (hc : c ≠ 0) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - graphResolvent M J Ω c) * (1 - resolventLowerCut (graphResolvent M J Ω 1) r) =
      cfc (fun s => min (graphComplementScalar c s) (graphComplementScalar c r))
        (graphResolvent M J Ω 1) * (1 - resolventLowerCut (graphResolvent M J Ω 1) r) := by
  let R := graphResolvent M J Ω 1
  let g := graphComplementScalar c
  let f := fun s => min (g s) (g r)
  let k := graphLowFactorScalar c r
  have hg : ContinuousOn g (spectrum ℝ R) := graphComplementScalar_continuousOn J Ω hc
  have hf : ContinuousOn f (spectrum ℝ R) := by
    have hp : ContinuousOn (fun s => (g s, g r)) (spectrum ℝ R) :=
      hg.prodMk continuousOn_const
    exact continuous_min.comp_continuousOn hp
  have hk : ContinuousOn k (spectrum ℝ R) := by
    apply continuousOn_const.div
      ((show ContinuousOn (graphScaleScalar c) (spectrum ℝ R) by
        unfold graphScaleScalar; fun_prop).mul continuousOn_const)
    intro s hs
    have hb := graphResolvent_spectrum_bounds J Ω hs
    exact mul_ne_zero (graphScaleScalar_pos hc hb.1 hb.2).ne'
      (graphScaleScalar_pos hc hr hr1).ne'
  have hid : cfc g R - cfc f R = cfc k R * resolventCutGenerator R r := by
    rw [← cfc_sub g f R hg hf, resolventCutGenerator,
      ← cfc_mul k (fun s : ℝ => max (r - s) 0) R hk (by fun_prop)]
    apply cfc_congr
    intro s hs
    have hb := graphResolvent_spectrum_bounds J Ω hs
    exact graphComplementScalar_clipping hc hr hr1 hb.1 hb.2
  have hz : (cfc g R - cfc f R) * (1 - resolventLowerCut R r) = 0 := by
    rw [hid, mul_assoc, resolventCutGenerator_mul_complement R
      (graphResolvent_positive J Ω 1).isSelfAdjoint, mul_zero]
  rw [sub_mul, sub_eq_zero] at hz
  rw [one_sub_graphResolvent_eq_cfc_scale J Ω hc]
  exact hz

theorem graphLowCut_bound (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c r : ℝ} (hc : c ≠ 0) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖(1 - resolventLowerCut (graphResolvent M J Ω 1) r) *
      (1 - graphResolvent M J Ω c)‖ ≤ graphComplementScalar c r := by
  let R := graphResolvent M J Ω 1
  let P := resolventLowerCut R r
  let f := fun s => min (graphComplementScalar c s) (graphComplementScalar c r)
  have hp : IsStarProjection P := resolventLowerCut_projection R r
  have hcomm : Commute P (graphResolvent M J Ω c) := by
    rw [graphResolvent_eq_cfc_scale J Ω hc]
    exact resolventLowerCut_commutes_cfc R (graphResolvent_positive J Ω 1).isSelfAdjoint r _
  have hcomm' : Commute (1 - P) (1 - graphResolvent M J Ω c) :=
    (Commute.one_right _).sub_right ((Commute.one_left _).sub_left hcomm)
  have hg0 := graphComplementScalar_nonneg hc hr hr1
  have hf : ‖cfc f R‖ ≤ graphComplementScalar c r := by
    apply norm_cfc_le hg0
    intro s hs
    have hb := graphResolvent_spectrum_bounds J Ω hs
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min
      (graphComplementScalar_nonneg hc hb.1 hb.2) hg0)]
    exact min_le_right _ _
  rw [hcomm'.eq, graphLowCut_clipped J Ω hc hr hr1]
  calc
    _ ≤ ‖cfc f R‖ * ‖1 - P‖ := norm_mul_le _ _
    _ ≤ graphComplementScalar c r * 1 :=
      mul_le_mul hf (hp.one_sub.norm_le _) (norm_nonneg _) hg0
    _ = _ := mul_one _

theorem graphLowCut_support (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    {c : ℝ} (hc : c ≠ 0) (r : ℝ) :
    (1 - resolventLowerCut (graphResolvent M J Ω 1) r) * (1 - graphResolvent M J Ω c) *
      (1 - resolventLowerCut (graphResolvent M J Ω 1) r) =
    (1 - resolventLowerCut (graphResolvent M J Ω 1) r) * (1 - graphResolvent M J Ω c) := by
  have hp := (resolventLowerCut_projection (graphResolvent M J Ω 1) r).one_sub
  have hcomm : Commute (resolventLowerCut (graphResolvent M J Ω 1) r)
      (graphResolvent M J Ω c) := by
    rw [graphResolvent_eq_cfc_scale J Ω hc]
    exact resolventLowerCut_commutes_cfc _ (graphResolvent_positive J Ω 1).isSelfAdjoint r _
  have hcomm' := (Commute.one_right _).sub_right ((Commute.one_left _).sub_left hcomm)
  rw [mul_assoc, ← hcomm'.eq, ← mul_assoc, hp.isIdempotentElem.eq]

end

end KadisonKastler

end OAI
