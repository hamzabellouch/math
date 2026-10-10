import OAI.Analysis.CircleDomains.Sobolev.LipschitzCurveLength
import OAI.Analysis.CircleDomains.Modulus.WeightedCurveLength
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace OAI

/-! The exact measure identity and arbitrary measurable weights for Lipschitz arclength. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity

lemma lipschitz_curve_length_map_measure {γ : ℝ → ℂ} {K : ℝ≥0} (hγ : LipschitzWith K γ)
    {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hi : InjOn γ S) :
    Measure.map (curveOnSet S γ)
      ((volume.restrict S).withDensity (fun t => ENNReal.ofReal ‖deriv γ t‖)) =
      (μH[1] : Measure ℂ).restrict (γ '' S) := by
  classical
  let g := curveOnSet S γ
  have hg : Measurable g := hγ.continuous.continuousOn.measurable_piecewise continuousOn_const hS
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
    ← lipschitz_curve_hausdorff_eq hγ hT (hb.subset inter_subset_left) (hi.mono inter_subset_left), him]

lemma weighted_lipschitz_curve_length {γ : ℝ → ℂ} {K : ℝ≥0} (hγ : LipschitzWith K γ)
    {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hi : InjOn γ S)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ z in γ '' S, q z ∂μH[1]) =
      ∫⁻ t in S, q (γ t)*ENNReal.ofReal ‖deriv γ t‖ := by
  classical
  let g := curveOnSet S γ
  have hg : Measurable g := hγ.continuous.continuousOn.measurable_piecewise continuousOn_const hS
  have hd : AEMeasurable (fun t => ENNReal.ofReal ‖deriv γ t‖) (volume.restrict S) :=
    ((measurable_deriv γ).norm.ennreal_ofReal).aemeasurable
  rw [← lipschitz_curve_length_map_measure hγ hS hb hi, lintegral_map hq hg,
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun t => q (g t)) hd (hq.comp hg).aemeasurable]
  apply setLIntegral_congr_fun hS
  intro t ht
  simp only [Pi.mul_apply, g, curveOnSet, piecewise_eq_of_mem S γ (fun _ => 0) ht, mul_comm]

end CircleDomainRigidity

end

end OAI
