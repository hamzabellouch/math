import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatCostAction

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile230
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_law_dual {K N : ℝ}
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
    IsProbabilityMeasure (densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₀)) ∧
    IsProbabilityMeasure (densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₁)) ∧
    ∀ (φ : X →ᵇ ℝ),HasCompactSupport (φ:X→ℝ) → GloballyLipschitz (φ:X→ℝ) →
      (∫ x,boundedHopfMap φ 1 x ∂densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₁))-
        (∫ x,φ x ∂densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u₀)) ≤
      quadraticWassersteinSq (μ₀:Measure X) (μ₁:Measure X)/(2*Real.exp (2*(K-a*CG)*T)) := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  refine ⟨hrcd.weighted_heat_probability hN hfull hfin o hVB h u₀ hun₀ hm₀ hT,
    hrcd.weighted_heat_probability hN hfull hfin o hVB h u₁ hun₁ hm₁ hT,?_⟩
  intro φ hφ hφL
  obtain ⟨D,hD⟩ := hφL
  obtain ⟨u,v,hu,hv,hcost⟩ := hHess.rcd_weighted_heat_hopf_cost hN hrcd hfull hfin o
    hF hFb hGb hGc ha h φ hφ hD hT
  have hac (w : Lp ℝ 2 ν) : densityMeasure ν w ≪ ν :=
    withDensity_absolutelyContinuous _ _
  have h0 : (∫ x,φ x ∂densityMeasure ν (cheegerHeat h T u₀)) =
      ∫ x,cheegerHeat h T u x ∂(μ₀:Measure X) := by
    rw [← integral_congr_ae ((hac _).ae_le hu),cheegerHeat_density_duality h u₀ u hT hun₀,
      he₀,integral_densityMeasure_L2 _ _ hun₀]
  have h1 : (∫ x,boundedHopfMap φ 1 x ∂densityMeasure ν (cheegerHeat h T u₁)) =
      ∫ x,cheegerHeat h T v x ∂(μ₁:Measure X) := by
    rw [← integral_congr_ae ((hac _).ae_le hv),cheegerHeat_density_duality h u₁ v hT hun₁,
      he₁,integral_densityMeasure_L2 _ _ hun₁]
  rw [h0,h1]
  exact hcost μ₀ μ₁ R hs₀ hs₁ C hC0 hCt hd₀ hd₁
end WeakHessian

end
end InlinedFile230

end OAI
