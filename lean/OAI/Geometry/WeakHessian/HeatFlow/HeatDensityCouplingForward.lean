import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatDensity
import OAI.Geometry.WeakHessian.Transport.DensityCouplingBound

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
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
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace

namespace WeakHessian
open WeakHessianFunctional WeakHessianTransport MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X} [IsProbabilityMeasure m]

lemma heatDensity_coupling_forward (h : QuadraticCheegerEnergy m)
    {u A : Lp ℝ 2 m} (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hmass : ∫ x, u x ∂m = 0) {ε B s t : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hεB : ε*B < 1)
    (hub : ∀ᵐ x ∂m, |u x| ≤ B) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = densityMeasure m (heatDensity h ε u t) ∧
      q.map Prod.snd = densityMeasure m (heatDensity h ε u s) ∧
      (∫⁻ p, (edist p.1 p.2)^2 ∂q) ≤
        ENNReal.ofReal ((2*ε^2/(1-ε*B)*(cheegerEnergy m (u : X → ℝ)).toReal)*(t-s)^2) := by
  have hd : 0 ≤ t-s := sub_nonneg.mpr hst
  have hα : 0 < 1-ε*B := sub_pos.mpr hεB
  have hp (r : ℝ) (hr : 0 ≤ r) : 0 ≤ s+(t-s)*r := by positivity
  have hc : ContinuousOn (fun r : ℝ => heatDensity h ε u (s+(t-s)*r)) (Icc 0 1) :=
    (heatDensity_continuousOn h ε hu).comp (by fun_prop)
      (fun r hr => hp r hr.1)
  have hpos (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
      ∀ᵐ x ∂m, 0 ≤ heatDensity h ε u (s+(t-s)*r) x :=
    (heatDensity_bounds h hε hB (hp r hr.1) u hub).mono fun _ hx => hα.le.trans hx.1
  have hlow (r : ℝ) (hr : r ∈ Ico (0:ℝ) 1) :
      ∀ᵐ x ∂m, 1-ε*B ≤ heatDensity h ε u (s+(t-s)*r) x :=
    (heatDensity_bounds h hε hB (hp r hr.1) u hub).mono fun _ hx => hx.1
  have hener (r : ℝ) (hr : r ∈ Ico (0:ℝ) 1) :
      (cheegerEnergy m (cheegerHeat h (s+(t-s)*r) u : X → ℝ)).toReal ≤
        (cheegerEnergy m (u : X → ℝ)).toReal :=
    ENNReal.toReal_mono hu.1.ne (cheegerHeat_energy_le h (hp r hr.1) u)
  obtain ⟨q,hq,hq0,hq1,hqb⟩ := density_coupling_bound m h hα hc hpos
    (fun r hr => heatDensity_mass h ε u hmass (hp r hr.1)) hlow
    (fun r _ => (cheeger_closedQuadraticEnergy h).formGenerator_heat m hu (s+(t-s)*r))
    hener (fun r hr => heatDensity_affine_deriv h ε hu hs hd hr.1)
  refine ⟨q,hq,?_,?_,?_⟩
  · simpa only [mul_one, add_sub_cancel] using hq0
  · simpa only [mul_zero, add_zero] using hq1
  · convert hqb using 1
    congr 1
    ring

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
