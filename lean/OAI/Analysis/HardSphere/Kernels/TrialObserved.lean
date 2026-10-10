import Mathlib
import OAI.Analysis.HardSphere.Kernels.TrialKernel
import OAI.Analysis.HardSphere.Bridges.GaussianMixture
import OAI.Analysis.HardSphere.Conditioning.RouteObservation

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
open Bridge Wiener GaussianPacking

lemma trialKernel_midpoint (t : ℝ) (y z u : Point) :
    ∀ᵐ ω ∂trialKernel t y z u,ω midpointTime=u := by
  rw [trialKernel_apply]
  apply (ae_map_iff ((trialPath_continuous t y z).measurable.comp
    (measurable_const.prodMk measurable_id)).aemeasurable (measurableSet_eq_fun ((continuous_eval_const midpointTime).measurable : Measurable (fun ω : C(Time,Point) ↦ ω midpointTime)) measurable_const)).mpr
  exact ae_of_all _ (fun β ↦ trial_midpoint t y z u β)

lemma paired_trial_midpoint (μ : Measure Point) [SFinite μ] (t : ℝ) (y z y' z' : Point)
    (S T : Set C(Time,Point)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ∀ᵐ p ∂pairedFactor μ (trialKernel t y z) (trialKernel t y' z') S T hS hT,
      p.2.1 midpointTime=p.1 ∧ p.2.2 midpointTime=p.1 := by
  apply pairedFactor_midpoint μ (trialKernel t y z) (trialKernel t y' z')
    (fun ω ↦ ω midpointTime) (fun ω ↦ ω midpointTime) id
    (continuous_eval_const midpointTime).measurable (continuous_eval_const midpointTime).measurable measurable_id
  · exact ae_of_all _ (trialKernel_midpoint t y z)
  · exact ae_of_all _ (trialKernel_midpoint t y' z')

lemma route_observed_trial_eq {W : Type*} [MeasurableSpace W] (d : ℕ)
    (τ : Fin (d+2) → Measure (Point×(C(Time,Point)×C(Time,Point))))
    [∀k,IsProbabilityMeasure (τ k)] (ξ : Measure W) [SFinite ξ]
    (hτ : ∀k,∀ᵐ p ∂τ k,p.2.1 midpointTime=p.1 ∧ p.2.2 midpointTime=p.1)
    (C : Set ((Fin (d+2) → Point×(C(Time,Point)×C(Time,Point)))×W)) :
    ((((Measure.pi τ).prod ξ) C)⁻¹ • ((Measure.pi τ).prod ξ).restrict C).map
      (observeFirst d (fun ω ↦ ω midpointTime)) =
    ((((Measure.pi τ).prod ξ) C)⁻¹ • ((Measure.pi τ).prod ξ).restrict C).map
      (observeSecond d (fun ω ↦ ω midpointTime)) := by
  apply conditioned_observed_measures_eq
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  have h : ∀k,∀ᵐ v ∂Measure.pi τ,(v k).2.1 midpointTime=(v k).1 ∧ (v k).2.2 midpointTime=(v k).1 :=
    fun k ↦ (measurePreserving_eval τ k).quasiMeasurePreserving.ae (hτ k)
  filter_upwards [ae_all_iff.mpr h] with v hv
  exact ae_of_all _ (fun _ ↦ hv)

end HardSphere.Comparison

end
end

end

end OAI
