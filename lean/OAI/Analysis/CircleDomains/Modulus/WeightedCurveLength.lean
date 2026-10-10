import OAI.Analysis.CircleDomains.Topology.CurveHausdorffLower
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace OAI

/-! The arclength identity as a measure identity and its weighted version. -/
open Set Function MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity

noncomputable def curveOnSet (S : Set ℝ) (γ : ℝ → ℂ) : ℝ → ℂ := by
  classical
  exact S.piecewise γ (fun _ => 0)

lemma curve_length_map_measure
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    (hi : InjOn γ D) {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hSD : S ⊆ D) :
    Measure.map (curveOnSet S γ)
      ((volume.restrict S).withDensity (fun t => ENNReal.ofReal ‖d t‖)) =
      (μH[1] : Measure ℂ).restrict (γ '' S) := by
  classical
  let g : ℝ → ℂ := curveOnSet S γ
  have hγ : ContinuousOn γ S := fun x hx => (hd x (hSD hx)).continuousAt.continuousWithinAt
  have hg : Measurable g := hγ.measurable_piecewise continuousOn_const hS
  apply Measure.ext
  intro B hB
  have hT : MeasurableSet (S ∩ g ⁻¹' B) := hS.inter (hg hB)
  have him : γ '' (S ∩ g ⁻¹' B) = B ∩ γ '' S := by
    ext z
    constructor
    · rintro ⟨t, ⟨ht, htB⟩, rfl⟩
      exact ⟨by simpa only [mem_preimage, g, curveOnSet, piecewise_eq_of_mem S γ (fun _ => 0) ht] using htB, ⟨t, ht, rfl⟩⟩
    · rintro ⟨hz, t, ht, rfl⟩
      refine ⟨t, ⟨ht, ?_⟩, rfl⟩
      simpa only [mem_preimage, g, curveOnSet, piecewise_eq_of_mem S γ (fun _ => 0) ht] using hz
  change Measure.map g _ B = _
  rw [Measure.map_apply hg hB, withDensity_apply _ (hg hB), Measure.restrict_restrict (hg hB),
    Measure.restrict_apply hB]
  rw [inter_comm (g ⁻¹' B) S, ← curve_hausdorff_eq_integral hD hd hc hi hT (hb.subset inter_subset_left)
    (inter_subset_left.trans hSD), him]

lemma weighted_curve_length
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    (hi : InjOn γ D) {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hSD : S ⊆ D)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ z in γ '' S, q z ∂μH[1]) =
      ∫⁻ t in S, q (γ t) * ENNReal.ofReal ‖d t‖ := by
  classical
  let g : ℝ → ℂ := curveOnSet S γ
  have hγ : ContinuousOn γ S := fun x hx => (hd x (hSD hx)).continuousAt.continuousWithinAt
  have hg : Measurable g := hγ.measurable_piecewise continuousOn_const hS
  have hdmeas : AEMeasurable (fun t => ENNReal.ofReal ‖d t‖) (volume.restrict S) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hc.mono hSD).norm).aemeasurable hS
  rw [← curve_length_map_measure hD hd hc hi hS hb hSD, lintegral_map hq hg,
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun t => q (g t)) hdmeas (hq.comp hg).aemeasurable]
  apply setLIntegral_congr_fun hS
  intro t ht
  simp only [Pi.mul_apply, g, curveOnSet, piecewise_eq_of_mem S γ (fun _ => 0) ht, mul_comm]

end CircleDomainRigidity

end

end OAI
