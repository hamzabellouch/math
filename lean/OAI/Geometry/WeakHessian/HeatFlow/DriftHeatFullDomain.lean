import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.DriftHeatGenerator
import OAI.Geometry.WeakHessian.LocalBounds.BoundedGraphCore

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile207
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_gradient_full_generator {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    {Cξ : ℝ}
    (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|ξ x| ≤ Cξ)
    (hξ0 : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ ξ x)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ x,ξ x*gamma (exponentialMeasure m (fun x => a*F x))
      (cheegerHeat h T f) (cheegerHeat h T f) x ∂exponentialMeasure m (fun x => a*F x)) ≤
    Real.exp (-(2*(K-a*CG))*T)*
      (∫ x,cheegerHeat h T ξ x*gamma (exponentialMeasure m (fun x => a*F x)) f f x
        ∂exponentialMeasure m (fun x => a*F x)) := by
  let V := fun x => a*F x
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  have hV := lipschitz_const_mul_real hF a
  have hVB : ∀ x,|V x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hVB
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal) hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  let : IsLocallyFiniteMeasure ν := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hnfin _ Metric.isBounded_ball⟩⟩
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp (|a| *CF)).toNNReal) (D := (Real.exp (|a| *CF)).toNNReal) hm hν
  obtain ⟨vs,As,hg,hvb,hAb,hvs,hAslim⟩ := cheeger_bounded_graph_core h hf
  have hglap (n : ℕ) : IsLaplacian ν (vs n) (As n) :=
    (hrcd.weighted_formGenerator_iff hfin o hVB h _ _).mpr (hg n)
  have hflap : IsLaplacian ν f Af := (hrcd.weighted_formGenerator_iff hfin o hVB h _ _).mpr hf
  have hright : Tendsto (fun n => ∫ x,cheegerHeat h T ξ x*gamma ν (vs n) (vs n) x ∂ν)
      atTop (𝓝 (∫ x,cheegerHeat h T ξ x*gamma ν f f x ∂ν)) := by
    apply graph_tendsto_gamma_bounded_pairing hnfin hnpar hglap hflap
    · simpa only [Lp.toLp_coeFn] using hvs
    · simpa only [Lp.toLp_coeFn] using hAslim
    · exact (Lp.memLp _).aestronglyMeasurable
    · exact cheegerHeat_bounded h hT hCξ ξ hξb
  have hheat (v : Lp ℝ 2 ν) := (cheegerHeat h T).continuous.tendsto v
  have hhlap (n : ℕ) : IsLaplacian ν (cheegerHeat h T (vs n)) (cheegerHeat h T (As n)) :=
    (hrcd.weighted_formGenerator_iff hfin o hVB h _ _).mpr (Q.formGenerator_heat ν (hg n) T)
  have hheatlap : IsLaplacian ν (cheegerHeat h T f) (cheegerHeat h T Af) :=
    (hrcd.weighted_formGenerator_iff hfin o hVB h _ _).mpr (Q.formGenerator_heat ν hf T)
  have hleft : Tendsto (fun n => ∫ x,ξ x*gamma ν (cheegerHeat h T (vs n)) (cheegerHeat h T (vs n)) x ∂ν)
      atTop (𝓝 (∫ x,ξ x*gamma ν (cheegerHeat h T f) (cheegerHeat h T f) x ∂ν)) := by
    apply graph_tendsto_gamma_bounded_pairing hnfin hnpar hhlap hheatlap
    · simpa only [Lp.toLp_coeFn,Function.comp_def] using (hheat f).comp hvs
    · simpa only [Lp.toLp_coeFn,Function.comp_def] using (hheat Af).comp hAslim
    · exact (Lp.memLp ξ).aestronglyMeasurable
    · exact hξb
  apply le_of_tendsto_of_tendsto hleft (hright.const_mul _) (Eventually.of_forall fun n => ?_)
  exact hHess.rcd_weighted_heat_gradient_generator hN hrcd hfull hfin o hF hFb hGb hGc ha h
    (hg n) (Nat.cast_nonneg n) hCξ (hvb n) hξb hξ0 hT
end WeakHessian

end
end InlinedFile207

end OAI
