import Mathlib
import OAI.Geometry.WeakHessian.Transport.CouplingCostBound
import OAI.Geometry.WeakHessian.HeatFlow.HeatDensityCouplingForward

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open Set Filter MeasureTheory Topology TopologicalSpace
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
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
open WeakHessianFunctional WeakHessianTransport MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X} [IsProbabilityMeasure m]

lemma heatDensity_coupling_cost (h : QuadraticCheegerEnergy m)
    {u A : Lp ℝ 2 m} (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hmass : ∫ x, u x ∂m = 0) {ε B b : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hεB : ε*B < 1)
    (hub : ∀ᵐ x ∂m, |u x| ≤ B) (hb : 0 ≤ b) :
    CouplingCostBound (fun r : Time => densityMeasure m (heatDensity h ε u (b*r)))
      ((2*ε^2/(1-ε*B)*(cheegerEnergy m (u : X → ℝ)).toReal)*b^2) := by
  intro s t
  rcases le_total (s:ℝ) (t:ℝ) with hst | hts
  · obtain ⟨q,hq,hq0,hq1,hqb⟩ := heatDensity_coupling_forward h hu hmass hε hB hεB hub
      (mul_nonneg hb s.2.1) (mul_le_mul_of_nonneg_left hst hb)
    refine ⟨q.map Prod.swap,⟨?_,?_⟩,?_⟩
    · rw [Measure.map_map measurable_fst measurable_swap]
      simpa only [Function.comp_def, Prod.fst_swap] using hq1
    · rw [Measure.map_map measurable_snd measurable_swap]
      simpa only [Function.comp_def, Prod.snd_swap] using hq0
    · rw [QuadraticTransportCost, lintegral_map
        ((continuous_fst.edist continuous_snd).measurable.pow_const 2) measurable_swap]
      simp only [Prod.fst_swap, Prod.snd_swap]
      simp_rw [edist_comm]
      convert hqb using 1
      congr 1
      change _ * |(s:ℝ)-(t:ℝ)|^2 = _
      rw [sq_abs]
      ring
  · obtain ⟨q,hq,hq0,hq1,hqb⟩ := heatDensity_coupling_forward h hu hmass hε hB hεB hub
      (mul_nonneg hb t.2.1) (mul_le_mul_of_nonneg_left hts hb)
    refine ⟨q,⟨hq0,hq1⟩,?_⟩
    change (∫⁻ p, (edist p.1 p.2)^2 ∂q) ≤ _
    convert hqb using 1
    congr 1
    change _ * |(s:ℝ)-(t:ℝ)|^2 = _
    rw [sq_abs]
    ring

lemma CurvatureDimension.heatDensity_testPlan {K N : ℝ} (hcd : CurvatureDimension m K N)
    (h : QuadraticCheegerEnergy m)
    {u A : Lp ℝ 2 m} (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hmass : ∫ x, u x ∂m = 0) {ε B b : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hεB : ε*B < 1)
    (hub : ∀ᵐ x ∂m, |u x| ≤ B) (hb : 0 ≤ b) :
    ∃ π : Measure (Curve X), IsTestPlan m π ∧ BoundedTracks π ∧
      (∀ r : Time, π.map (fun γ => γ r) = densityMeasure m (heatDensity h ε u (b*r))) ∧
      (∀ r : Time, π.map (fun γ => γ r) ≤ ENNReal.ofReal (1+ε*B) • m) ∧
      (∫⁻ γ, ∫⁻ r in Icc (0:ℝ) 1, (metricSpeed γ r)^2 ∂volume ∂π) ≤
        ENNReal.ofReal ((2*ε^2/(1-ε*B)*(cheegerEnergy m (u : X → ℝ)).toReal)*b^2) := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure m
  let ρ : Time → Lp ℝ 2 m := fun r => heatDensity h ε u (b*r)
  have hpos (r : Time) : ∀ᵐ x ∂m, 0 ≤ ρ r x :=
    (heatDensity_bounds h hε hB (mul_nonneg hb r.2.1) u hub).mono
      fun _ hx => (sub_pos.mpr hεB).le.trans hx.1
  have hm (r : Time) : ∫ x, ρ r x ∂m = 1 :=
    heatDensity_mass h ε u hmass (mul_nonneg hb r.2.1)
  let μ : Time → ProbabilityMeasure X := fun r => densityProbability m (ρ r) (hpos r) (hm r)
  have hρ : Continuous ρ := (heatDensity_continuousOn h ε hu).comp_continuous
    (by fun_prop : Continuous (fun r : Time => b*(r:ℝ)))
    (fun r => mul_nonneg hb r.2.1)
  have hμ : Continuous μ := continuous_densityProbability m hρ hpos hm
  have hcomp (r : Time) : (μ r : Measure X) ≤ ENNReal.ofReal (1+ε*B) • m :=
    densityMeasure_le m ((heatDensity_bounds h hε hB (mul_nonneg hb r.2.1) u hub).mono fun _ hx => hx.2)
  have hcomp' : ∃ L : ℝ≥0, ∀ r : Time, (μ r : Measure X) ≤ (L:ℝ≥0∞) • m := by
    refine ⟨⟨1+ε*B,by positivity⟩,?_⟩
    intro r
    convert hcomp r using 1
    congr 1
    exact (ENNReal.ofReal_eq_coe_nnreal (by positivity : 0 ≤ 1+ε*B)).symm
  obtain ⟨π,hπ,htrack,hmarg,hact⟩ := hcd.testPlan_of_cost μ hμ
    (by positivity : 0 ≤ (2*ε^2/(1-ε*B)*(cheegerEnergy m (u : X → ℝ)).toReal)*b^2)
    (heatDensity_coupling_cost h hu hmass hε hB hεB hub hb) hcomp'
  refine ⟨π,hπ,htrack,hmarg,?_,hact⟩
  intro r
  rw [hmarg]
  exact hcomp r

end WeakHessian

end

end OAI
