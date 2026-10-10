import OAI.Analysis.CircleDomains.Sobolev.DifferentiableCurveLength
import OAI.Analysis.CircleDomains.Modulus.WeightedCurveLength
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace OAI

/-! Weighted arclength on a bounded Borel parameter set with actual within-set derivatives. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity

lemma differentiable_curve_length_map_measure {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hi : InjOn γ S)
    (hd : ∀ t ∈ S, HasFDerivWithinAt γ (d t) S t) :
    Measure.map (curveOnSet S γ)
      ((volume.restrict S).withDensity (fun t => ENNReal.ofReal ‖d t‖)) =
      (μH[1] : Measure ℂ).restrict (γ '' S) := by
  classical
  let g := curveOnSet S γ
  have hc : ContinuousOn γ S := fun t ht => (hd t ht).continuousWithinAt
  have hg : Measurable g := hc.measurable_piecewise continuousOn_const hS
  apply Measure.ext
  intro B hB
  have hT : MeasurableSet (S ∩ g ⁻¹' B) := hS.inter (hg hB)
  have him : γ '' (S ∩ g ⁻¹' B) = B ∩ γ '' S := by
    ext z
    constructor
    · rintro ⟨t, ⟨ht, htB⟩, rfl⟩
      exact ⟨by simpa only [mem_preimage, g, curveOnSet, piecewise_eq_of_mem S γ (fun _ => 0) ht] using htB,
        ⟨t, ht, rfl⟩⟩
    · rintro ⟨hz, t, ht, rfl⟩
      refine ⟨t, ⟨ht, ?_⟩, rfl⟩
      simpa only [mem_preimage, g, curveOnSet, piecewise_eq_of_mem S γ (fun _ => 0) ht] using hz
  change Measure.map g _ B = _
  rw [Measure.map_apply hg hB, withDensity_apply _ (hg hB),
    Measure.restrict_restrict (hg hB), Measure.restrict_apply hB]
  rw [inter_comm (g ⁻¹' B) S,
    ← differentiable_curve_hausdorff_eq hT (hb.subset inter_subset_left)
      (fun t ht => (hd t ht.1).mono inter_subset_left) (hi.mono inter_subset_left), him]

lemma weighted_differentiable_curve_length {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hi : InjOn γ S)
    (hd : ∀ t ∈ S, HasFDerivWithinAt γ (d t) S t)
    (hm : AEMeasurable (fun t => ENNReal.ofReal ‖d t‖) (volume.restrict S))
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ z in γ '' S, q z ∂μH[1]) =
      ∫⁻ t in S, q (γ t)*ENNReal.ofReal ‖d t‖ := by
  classical
  let g := curveOnSet S γ
  have hc : ContinuousOn γ S := fun t ht => (hd t ht).continuousWithinAt
  have hg : Measurable g := hc.measurable_piecewise continuousOn_const hS
  rw [← differentiable_curve_length_map_measure hS hb hi hd, lintegral_map hq hg,
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun t => q (g t)) hm (hq.comp hg).aemeasurable]
  apply setLIntegral_congr_fun hS
  intro t ht
  simp only [Pi.mul_apply, g, curveOnSet, piecewise_eq_of_mem S γ (fun _ => 0) ht, mul_comm]

end CircleDomainRigidity

end

end OAI
