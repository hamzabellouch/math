import Mathlib
import OAI.Geometry.WeakHessian.Transport.DynamicActionBoundProper

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
open WeakHessianFunctional WeakHessianTransport MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m ν : Measure X}

lemma CurvatureDimension.testPlan_of_cost_reference [Nonempty X] {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    (μ : Time → ProbabilityMeasure X) (hμ : Continuous μ)
    {C : ℝ} (hC : 0 ≤ C) (hcost : CouplingCostBound (fun t => (μ t:Measure X)) C)
    (hcomp : ∃ L : ℝ≥0, ∀ t : Time,(μ t:Measure X) ≤ (L:ℝ≥0∞) • ν) :
    ∃ π : Measure (Curve X), IsTestPlan ν π ∧
      (∀ t : Time,π.map (fun γ => γ t) = (μ t:Measure X)) ∧
      (∫⁻ γ,∫⁻ t in Icc (0:ℝ) 1,(metricSpeed γ t)^2 ∂volume ∂π) ≤ ENNReal.ofReal C := by
  apply exists_proper_testPlan_superposition ν μ hμ hC _ hcomp
  apply hcd.dynamicActionBound_proper μ _ hcost
  obtain ⟨L,hL⟩ := hcomp
  intro t
  exact (Measure.absolutelyContinuous_of_le_smul (hL t)).trans hν

variable [IsProbabilityMeasure ν]
lemma CurvatureDimension.prox_testPlan {K N : ℝ} (hcd : CurvatureDimension m K N) (hν : ν ≪ m)
    {u v D : Lp ℝ 2 ν} {t : ℝ} (h : RelaxedProx u t v D)
    (hmass : ∫ x,u x ∂ν = 0) {ε B : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hεB : ε*B < 1)
    (hu : ∀ᵐ x ∂ν, |u x| ≤ B) (hv : ∀ᵐ x ∂ν, |v x| ≤ B) :
    ∃ π : Measure (Curve X), IsTestPlan ν π ∧
      (∀ r : Time, π.map (fun γ => γ r) = densityMeasure ν (linearDensity ε u v r)) ∧
      (∀ r : Time, π.map (fun γ => γ r) ≤ ENNReal.ofReal (1+ε*B) • ν) ∧
      (∫⁻ γ,∫⁻ r in Icc (0:ℝ) 1,(metricSpeed γ r)^2 ∂volume ∂π) ≤
        ENNReal.ofReal (ε^2/(1-ε*B)*(t^2*‖D‖)^2) := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure ν
  let ρ : Time → Lp ℝ 2 ν := fun r => linearDensity ε u v r
  have hpos (r : Time) : ∀ᵐ x ∂ν,0 ≤ ρ r x :=
    (linearDensity_bounds hε hB r.2 hu hv).mono fun _ hx => (sub_pos.mpr hεB).le.trans hx.1
  have hm (r : Time) : ∫ x,ρ r x ∂ν = 1 := linearDensity_mass ε u v hmass (h.mass.trans hmass) _
  let μ : Time → ProbabilityMeasure X := fun r => densityProbability ν (ρ r) (hpos r) (hm r)
  have hρ : Continuous ρ := (continuous_linearDensity ε u v).comp continuous_subtype_val
  have hμ : Continuous μ := continuous_boundedDensityProbability ν hρ hpos hm
  have hcomp (r : Time) : (μ r:Measure X) ≤ ENNReal.ofReal (1+ε*B) • ν :=
    densityMeasure_le ν ((linearDensity_bounds hε hB r.2 hu hv).mono fun _ hx => hx.2)
  have hcomp' : ∃ L : ℝ≥0, ∀ r : Time,(μ r:Measure X) ≤ (L:ℝ≥0∞) • ν := by
    exact ⟨Real.toNNReal (1+ε*B), hcomp⟩
  obtain ⟨π,hπ,hmarg,hact⟩ := hcd.testPlan_of_cost_reference hν μ hμ
    (by positivity : 0 ≤ ε^2/(1-ε*B)*(t^2*‖D‖)^2)
    (prox_linearDensity_coupling_cost h hmass hε hB hεB hu hv) hcomp'
  exact ⟨π,hπ,hmarg,fun r => by rw [hmarg]; exact hcomp r,hact⟩
end WeakHessian

open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

end
end InlinedFile0

end OAI
