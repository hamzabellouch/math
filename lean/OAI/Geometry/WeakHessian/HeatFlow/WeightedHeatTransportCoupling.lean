import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatLawDual
import OAI.Geometry.WeakHessian.Calculus.CompactHopfDualLimit

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
section InlinedFile232
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_transport_coupling {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (u₀ u₁ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)))
    (hun₀ : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ u₀ x)
    (hun₁ : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ u₁ x)
    (hm₀ : ∫ x,u₀ x ∂exponentialMeasure m (fun x => a*F x) = 1)
    (hm₁ : ∫ x,u₁ x ∂exponentialMeasure m (fun x => a*F x) = 1)
    (μ₀ μ₁ : ProbabilityMeasure X)
    (he₀ : (μ₀:Measure X) = densityMeasure (exponentialMeasure m (fun x => a*F x)) u₀)
    (he₁ : (μ₁:Measure X) = densityMeasure (exponentialMeasure m (fun x => a*F x)) u₁)
    (R : ℝ≥0) (hs₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hs₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₁) ∧
      q.map Prod.snd = densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₀) ∧
      (∫⁻ p,(edist p.1 p.2)^2 ∂q) ≤
        ENNReal.ofReal (quadraticWassersteinSq (μ₀:Measure X) (μ₁:Measure X)/Real.exp (2*(K-a*CG)*T)) := by
  obtain ⟨hp₀,hp₁,hd⟩ := hHess.rcd_weighted_heat_law_dual hN hrcd hfull hfin o
    hF hFb hGb hGc ha h u₀ u₁ hun₀ hun₁ hm₀ hm₁ μ₀ μ₁ he₀ he₁ R hs₀ hs₁ hC0 hCt hd₀ hd₁ hT
  let := hp₀
  let := hp₁
  apply exists_proper_coupling_cost_of_compact_hopf_bound _ _ o
  intro φ hc hLφ
  convert hd φ hc hLφ using 1
  ring
end WeakHessian

end
end InlinedFile232

end

end OAI
