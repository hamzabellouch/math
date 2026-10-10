import OAI.Analysis.CircleDomains.Sobolev.WeakProbabilityMeasurability
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

namespace OAI

/-! Only the measurable inclusion of a compact weak family is needed for
Riesz representation. No replacement of the evaluation sigma algebra is made. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace CircleDomainRigidity

lemma measurable_measure_of_continuous_finite
    {X Z : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [HasOuterApproxClosed Z]
    {F : X → FiniteMeasure Z} (hF : Continuous F) :
    Measurable (fun x => (F x : Measure Z)) := by
  apply Measurable.measure_of_isPiSystem
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
  · intro S hS
    apply measurable_of_tendsto_metrizable
      (fun n => ((FiniteMeasure.continuous_lintegral_boundedContinuousFunction
        (hS.apprSeq n)).comp hF).measurable)
    apply tendsto_pi_nhds.mpr
    intro x
    exact HasOuterApproxClosed.tendsto_lintegral_apprSeq hS (F x : Measure Z)
  · simpa only [← FiniteMeasure.ennreal_mass,Function.comp_def] using
      (ENNReal.continuous_coe.comp (FiniteMeasure.continuous_mass.comp hF)).measurable

lemma compact_finiteMeasure_measurable_le_borel
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [HasOuterApproxClosed Z] (S : Set (FiniteMeasure Z)) :
    (inferInstance : MeasurableSpace S) ≤ borel S := by
  have h : @Measurable S (Measure Z) (borel S) inferInstance
      (fun v => (v.val : Measure Z)) := by
    let : MeasurableSpace S := borel S
    let : BorelSpace S := ⟨rfl⟩
    exact measurable_measure_of_continuous_finite continuous_subtype_val
  change ((inferInstance : MeasurableSpace (Measure Z)).comap
    (fun v : FiniteMeasure Z => (v : Measure Z))).comap
      (fun v : S => v.val) ≤ borel S
  simpa only [MeasurableSpace.comap_comp,Function.comp_def] using h.comap_le

lemma measurable_finiteMeasure_integral
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (f : Z →ᵇ ℝ) : Measurable (fun v : FiniteMeasure Z => ∫ z, f z ∂(v : Measure Z)) := by
  have hv : Measurable (fun v : FiniteMeasure Z => (v : Measure Z)) := measurable_subtype_coe
  have hp := ((Measure.measurable_lintegral f.nnrealPart.measurable_coe_ennreal_comp).comp
    hv).ennreal_toReal
  have hn := ((Measure.measurable_lintegral (-f).nnrealPart.measurable_coe_ennreal_comp).comp
    hv).ennreal_toReal
  convert hp.sub hn using 1
  funext v
  rw [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub]
  simp only [Pi.sub_apply,Function.comp_def]
  rw [BoundedContinuousFunction.toReal_lintegral_coe_eq_integral,
    BoundedContinuousFunction.toReal_lintegral_coe_eq_integral]

end CircleDomainRigidity

end

end OAI
