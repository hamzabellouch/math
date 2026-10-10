import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ContinuousTimeMarginals

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

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
open Set MeasureTheory Filter
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter Topology Bornology
open scoped InnerProductSpace


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal


open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal


open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory


namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma IsCoupling.interpolation_endpoints {π : Measure (Curve X)} {μ₀ μ₁ : Measure X}
    (h : IsCoupling (endpointCoupling π) μ₀ μ₁) :
    interpolation π timeZero = μ₀ ∧ interpolation π timeOne = μ₁ := by
  have hm : Measurable (fun γ : Curve X => (γ timeZero, γ timeOne)) :=
    (continuous_eval_const timeZero).measurable.prodMk
      (continuous_eval_const timeOne).measurable
  simpa only [IsCoupling, endpointCoupling, Measure.map_map measurable_fst hm,
    Measure.map_map measurable_snd hm, Function.comp_def, interpolation] using h

omit [MeasurableSpace X] [BorelSpace X] in
lemma IsGeodesic.hasControlBound {γ : Curve X} (h : IsGeodesic γ) :
    HasControlBound γ (dist (γ timeZero) (γ timeOne)) := by
  have hc : IsSquareControl γ (fun _ => dist (γ timeZero) (γ timeOne)) := by
    refine ⟨measurable_const,memLp_const _,ae_of_all _ (fun _ => dist_nonneg),?_⟩
    intro s t hst
    rw [h s t, intervalIntegral.integral_const, smul_eq_mul,
      abs_sub_comm (s:ℝ), abs_of_nonneg (sub_nonneg.mpr hst)]
  have H := hasControlBound_of_squareControl hc
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, ENNReal.toReal_one, smul_eq_mul, one_mul,
    Real.sqrt_sq dist_nonneg] using H

omit [MeasurableSpace X] [BorelSpace X] in
lemma IsGeodesic.kineticAction_le {γ : Curve X} (h : IsGeodesic γ) :
    kineticAction γ ≤ (edist (γ timeZero) (γ timeOne))^2 := by
  rw [edist_dist]
  exact pow_le_pow_left₀ bot_le (controlNorm_le h.hasControlBound) 2

lemma geodesic_plan_action_le_cost [SecondCountableTopology X] {π : Measure (Curve X)}
    (h : ∀ᵐ γ ∂π, IsGeodesic γ) :
    (∫⁻ γ, kineticAction γ ∂π) ≤ QuadraticTransportCost (endpointCoupling π) := by
  rw [QuadraticTransportCost, endpointCoupling, lintegral_map
    ((continuous_fst.edist continuous_snd).measurable.pow_const 2)
    ((continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable)]
  exact lintegral_mono_ae (h.mono fun γ hγ => hγ.kineticAction_le)

omit [BorelSpace X] in
lemma hasSecondMoment_of_compact [CompactSpace X] [Nonempty X]
    (μ : Measure X) [IsProbabilityMeasure μ] : HasSecondMoment μ := by
  let o : X := Classical.arbitrary X
  obtain ⟨R,hR⟩ := (isCompact_univ : IsCompact (univ : Set X)).isBounded.subset_closedBall o
  refine ⟨o,?_⟩
  calc
    (∫⁻ x, (edist x o)^2 ∂μ) ≤ ∫⁻ x, (ENNReal.ofReal R)^2 ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [edist_dist]
      exact pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal (hR (mem_univ x))) 2
    _ < ∞ := by simp

def CouplingCostBound (μ : Time → Measure X) (C : ℝ) : Prop :=
  ∀ s t : Time, ∃ q : Measure (X×X), IsCoupling q (μ s) (μ t) ∧
    QuadraticTransportCost q ≤ ENNReal.ofReal (C*(dist s t)^2)

lemma CurvatureDimension.dynamicActionBound [CompactSpace X] [Nonempty X]
    {m : Measure X} {K N : ℝ} (hcd : CurvatureDimension m K N)
    (μ : Time → ProbabilityMeasure X) (hac : ∀ t, (μ t:Measure X) ≪ m)
    {C : ℝ} (hcost : CouplingCostBound (fun t => (μ t:Measure X)) C) :
    DynamicActionBound (fun t => (μ t:Measure X)) C := by
  intro s t
  obtain ⟨π,hπ,hgeo,hopt,_⟩ := hcd (μ s) (μ t) (by infer_instance) (by infer_instance)
    (hasSecondMoment_of_compact _) (hasSecondMoment_of_compact _) (hac s) (hac t)
  obtain ⟨q,hq,hqb⟩ := hcost s t
  obtain ⟨h0,h1⟩ := hopt.1.interpolation_endpoints
  exact ⟨π,hπ,h0,h1,(geodesic_plan_action_le_cost hgeo).trans ((hopt.2 q hq).trans hqb)⟩

lemma CurvatureDimension.testPlan_of_cost [CompactSpace X] [Nonempty X]
    {m : Measure X} {K N : ℝ} (hcd : CurvatureDimension m K N)
    (μ : Time → ProbabilityMeasure X) (hμ : Continuous μ)
    {C : ℝ} (hC : 0 ≤ C) (hcost : CouplingCostBound (fun t => (μ t:Measure X)) C)
    (hcomp : ∃ L : ℝ≥0, ∀ t : Time, (μ t : Measure X) ≤ (L:ℝ≥0∞) • m) :
    ∃ π : Measure (Curve X), IsTestPlan m π ∧ BoundedTracks π ∧
      (∀ t : Time, π.map (fun γ => γ t) = (μ t : Measure X)) ∧
      (∫⁻ γ, ∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2 ∂volume ∂π) ≤ ENNReal.ofReal C := by
  apply exists_testPlan_superposition m μ hμ hC _ hcomp
  apply hcd.dynamicActionBound μ _ hcost
  obtain ⟨L,hL⟩ := hcomp
  intro t
  exact (Measure.absolutelyContinuous_of_le (hL t)).trans (Measure.smul_absolutelyContinuous)

end WeakHessian

end

end OAI
