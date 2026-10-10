import Mathlib
import OAI.Geometry.WeakHessian.Measure.OptimalTimeLawSupported
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatEndpointAction

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile227
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_hopf_cost {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (φ : X →ᵇ ℝ) (hφ : HasCompactSupport (φ : X → ℝ)) {D : ℝ≥0} (hφL : LipschitzWith D φ)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ u v : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)),
      u =ᵐ[exponentialMeasure m (fun x => a*F x)] φ ∧
      v =ᵐ[exponentialMeasure m (fun x => a*F x)] boundedHopfMap φ 1 ∧
      ∀ (μ₀ μ₁ : ProbabilityMeasure X) (R : ℝ≥0),
        (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0 →
        (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0 →
        ∀ C : ℝ≥0∞,C ≠ 0 → C ≠ ∞ →
        (μ₀:Measure X) ≤ C • m → (μ₁:Measure X) ≤ C • m →
        (∫ x,cheegerHeat h T v x ∂(μ₁:Measure X))-
          (∫ x,cheegerHeat h T u x ∂(μ₀:Measure X)) ≤
        quadraticWassersteinSq (μ₀:Measure X) (μ₁:Measure X)/(2*Real.exp (2*(K-a*CG)*T)) := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  obtain ⟨u,v,hu,hv,hA⟩ := hHess.rcd_weighted_heat_endpoint_action hN hrcd hfull hfin o
    hF hFb hGb hGc ha h φ hφ hφL hT
  refine ⟨u,v,hu,hv,?_⟩
  intro μ₀ μ₁ R hs₀ hs₁ C hC0 hCt hd₀ hd₁
  obtain ⟨π,hπ,hb,hg,ho,_,_,_⟩ :=
    hrcd.1.exists_entropy_testPlan hN hfin μ₀ μ₁ o R hs₀ hs₁ hC0 hCt hd₀ hd₁
  have hp : IsTestPlan ν (π:Measure (Curve X)) :=
    hπ.of_measure_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
      (exponentialMeasure_comparable (m := m) hVB).1
  have H := hA π hp hb hg
  obtain ⟨B,hB⟩ := hp.2.1
  have hmap (w : Lp ℝ 2 ν) (t : Time) :
      (∫ x,cheegerHeat h T w x ∂interpolation (π:Measure (Curve X)) t) =
        ∫ γ,cheegerHeat h T w (γ t) ∂(π:Measure (Curve X)) :=
    integral_map (continuous_eval_const t).measurable.aemeasurable
      ((Lp.aestronglyMeasurable _).mono_ac (Measure.absolutelyContinuous_of_le_smul (hB t)))
  obtain ⟨he₀,he₁⟩ := ho.1.interpolation_endpoints
  rw [← hmap v timeOne,← hmap u timeZero,he₀,he₁] at H
  have hcost : quadraticWassersteinSq (μ₀:Measure X) (μ₁:Measure X) =
      ∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂(π:Measure (Curve X)) := by
    rw [ho.quadraticWassersteinSq_eq,endpointCost_eq_ofReal_integral π o R hg ho.1 hs₀ hs₁,
      ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  rwa [hcost]
end WeakHessian

end
end InlinedFile227

end OAI
