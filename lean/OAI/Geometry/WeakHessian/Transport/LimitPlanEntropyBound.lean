import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.Law
import OAI.Geometry.WeakHessian.Entropy.ClosedEntropyAlong

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
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

namespace CDEnvironment
variable (env : CDEnvironment m K N)

lemma limitPlan_entropy_bound (c : EntropyCell m K N) (t : Time) :
    entropyReal m (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) ≤
      (1-(t:ℝ))*entropyReal m (c.leftLaw:Measure X)+(t:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((t:ℝ)*(1-(t:ℝ)))*planEnergy ((env.limitPlan c).law:Measure (Curve X)) := by
  let Q := Metric.closedBall c.center (3*(c.radius:ℝ))
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using env.finite_bounded Q Metric.isBounded_closedBall⟩
  let p := (env.limitPlan c).law
  have hs (s : Time) : ∀ᵐ x ∂(lawAt p s:Measure X), x ∈ Q :=
    ae_iff.mpr (env.limitPlan_supported c s)
  have hd (s : Time) : (lawAt p s:Measure X) ≤ c.uniformCap • m.restrict Q := by
    have H := Measure.restrict_mono_measure (env.limitPlan_dominated c s) Q
    change (lawAt p s:Measure X).restrict Q ≤ (c.uniformCap • m).restrict Q at H
    rwa [Measure.restrict_eq_self_of_ae_mem (hs s),Measure.restrict_smul] at H
  have he (s : Time) : entropyReal (m.restrict Q) (lawAt p s:Measure X) =
      entropyReal m (lawAt p s:Measure X) :=
    entropyReal_restrict_reference Metric.isClosed_closedBall.measurableSet
      (env.limitPlan_finite_entropy c s).1 (hs s)
  let a : Time → ℝ := fun s =>
      (1-(s:ℝ))*entropyReal m (c.leftLaw:Measure X)+(s:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((s:ℝ)*(1-(s:ℝ)))*planEnergy (p:Measure (Curve X))
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hc : IsClosed {s | entropyReal m (lawAt p s:Measure X) ≤ a s} := by
    simp_rw [← he]
    exact isClosed_entropy_le_along (lawAt p) (continuous_lawAt_time p) c.uniformCap_finite hd a ha
  have hdy : (⋃ n, dyadicTimes n) ⊆ {s | entropyReal m (lawAt p s:Measure X) ≤ a s} := by
    intro s hs
    obtain ⟨n,hn⟩ := mem_iUnion.mp hs
    exact env.limitPlan_entropy_bound_dyadic c n s hn
  exact (closure_minimal hdy hc) (dense_dyadicTimes t)

end CDEnvironment
end WeakHessian

end
end InlinedFile0

end OAI
