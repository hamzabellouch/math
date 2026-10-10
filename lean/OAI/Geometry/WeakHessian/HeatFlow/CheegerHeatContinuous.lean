import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeat
import OAI.Geometry.WeakHessian.HeatFlow.RealHeatRangeError

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

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_continuousOn (hfinite : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) :
    ContinuousOn (fun t : ℝ => cheegerHeat h t u) (Ici 0) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  let Q := cheeger_closedQuadraticEnergy h
  have hd : Dense (Q.resolventLinear.toLinearMap.range : Set (Lp ℝ 2 m)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (Q.resolvent_range_dense (cheeger_domain_dense h))
  apply continuousOn_of_uniform_approx_of_continuousOn
  intro U hU
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_uniformity_dist.mp hU
  obtain ⟨v,⟨w,rfl⟩,hw⟩ := hd.exists_dist_lt u hε
  refine ⟨fun t => cheegerHeat h t (Q.resolvent w), ?_, ?_⟩
  · exact (Q.heat_lipschitz_on_generator m (Q.isFormGenerator_resolvent w)).continuousOn
  · intro t ht
    apply hεU
    change dist u (Q.resolvent w) < ε at hw
    exact (cheegerHeat_contractive h ht u (Q.resolvent w)).trans_lt hw

lemma cheegerHeat_integral_generator (hfinite : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in 0..t, cheegerHeat h s A) = cheegerHeat h t u-u := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  have hc := cheegerHeat_continuousOn hfinite h A
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    ((cheegerHeat_continuousOn hfinite h u).mono Icc_subset_Ici_self)
    (fun s hs => ((cheeger_closedQuadraticEnergy h).heat_deriv_form_right m (cheeger_domain_dense h) hu hs.1.le).mono Ioi_subset_Ici_self)
    ((hc.mono (show uIcc (0:ℝ) t ⊆ Ici 0 by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable)
  change (∫ s in 0..t, cheegerHeat h s A) = cheegerHeat h t u-cheegerHeat h 0 u at H
  simpa only [cheegerHeat_zero, one_apply_eq_self] using H
end WeakHessian

end
end InlinedFile0

end OAI
