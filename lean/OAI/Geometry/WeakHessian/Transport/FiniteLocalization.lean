import Mathlib
import OAI.Geometry.WeakHessian.Calculus.IntegralEvalDifference

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma IsTestPlan.finite_localization (hfinite : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π) :
    ∃ S : Set X, MeasurableSet S ∧ IsFiniteMeasure (m.restrict S) ∧
      IsTestPlan (m.restrict S) π := by
  obtain ⟨o,R,hR,hb⟩ := hb
  let S := Metric.closedBall o R
  have hS : MeasurableSet S := measurableSet_closedBall
  have hfin : IsFiniteMeasure (m.restrict S) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hfinite _ Metric.isBounded_closedBall⟩
  refine ⟨S,hS,hfin,hπ.1,?_,hπ.2.2⟩
  obtain ⟨C,hC⟩ := hπ.2.1
  refine ⟨C,fun t => ?_⟩
  have ha : ∀ᵐ x ∂(π.map (fun γ => γ t)), x ∈ S := by
    apply ae_map_iff (continuous_eval_const t).measurable.aemeasurable hS |>.mpr
    exact hb.mono fun γ hγ => hγ t
  rw [← Measure.restrict_eq_self_of_ae_mem ha]
  convert Measure.restrict_mono le_rfl (hC t) using 1
  exact (Measure.restrict_smul _ _ _).symm

lemma IsTestPlan.continuous_integral_eval_bounded (hfinite : FiniteOnBoundedSets m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π) (hb : BoundedTracks π)
    {f : X → ℝ} (hf : AEMeasurable f m) {B : ℝ} (hB : ∀ᵐ x ∂m, |f x| ≤ B) :
    Continuous (fun t : Time => ∫ γ, f (γ t) ∂π) := by
  obtain ⟨S,hS,hfin,hplan⟩ := hπ.finite_localization hfinite hb
  let : IsFiniteMeasure (m.restrict S) := hfin
  apply hplan.continuous_integral_eval
  exact (integrable_const B).mono' hf.restrict.aestronglyMeasurable
    (ae_restrict_of_ae (hB.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx))

end WeakHessian

end
end InlinedFile0

end OAI
