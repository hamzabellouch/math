import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatGradientTest
import OAI.Geometry.WeakHessian.HeatFlow.ResolventGraphConvergence
import OAI.Geometry.WeakHessian.LocalBounds.GraphGammaPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile205
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_heat_gradient_generator {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {f Af ξ : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    {Cf Cξ : ℝ} (hCf : 0 ≤ Cf)
    (hCξ : 0 ≤ Cξ)
    (hfb : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|f x| ≤ Cf)
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
  let ts : ℕ → ℝ := fun n => ((n:ℝ)+1)⁻¹
  have hts (n : ℕ) : 0 < ts n := by dsimp [ts]; positivity
  have ht0 : Tendsto ts atTop (𝓝 0) := by
    simpa only [ts,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let R := fun n => (Q.scale (hts n)).resolventLinear
  choose vs As AAs he hg hAg hvb hAb hAAb using
    (fun n => cheeger_double_resolvent_core h (hts n) hCf f hfb)
  have hRgraph := cheeger_double_resolvent_graph_tendsto h hf hts ht0
  have hAs (n : ℕ) : As n = R n (R n Af) := by
    apply Q.formGenerator_unique (cheeger_domain_dense h) (hg n)
    rw [he n]
    exact hRgraph.1 n
  have hvs : Tendsto vs atTop (𝓝 f) := hRgraph.2.1.congr (fun n => (he n).symm)
  have hAslim : Tendsto As atTop (𝓝 Af) := hRgraph.2.2.congr (fun n => (hAs n).symm)
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
  exact hHess.rcd_weighted_heat_gradient_bounded_test hN hrcd hfull hfin o hF hFb hGb hGc ha h
    (hg n) (hAg n) hCf (by positivity) (by positivity) hCξ (hvb n) (hAb n) (hAAb n) hξb hξ0 hT
end WeakHessian

end
end InlinedFile205

end OAI
