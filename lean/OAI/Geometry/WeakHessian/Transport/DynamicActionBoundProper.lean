import Mathlib
import OAI.Geometry.WeakHessian.Entropy.LinearDensity
import OAI.Geometry.WeakHessian.Transport.BoundedHopfLpDual
import OAI.Geometry.WeakHessian.LocalBounds.SuperpositionProper
import OAI.Geometry.WeakHessian.LocalBounds.Young
import OAI.Geometry.WeakHessian.Transport.LiftBoundedCoupling

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
open Set Filter MeasureTheory
open scoped ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] [Nonempty X]

lemma CurvatureDimension.dynamicActionBound_proper {m : Measure X} {K N : ℝ}
    (hcd : CurvatureDimension m K N) (μ : Time → ProbabilityMeasure X)
    (hac : ∀ t,(μ t:Measure X) ≪ m)
    {C : ℝ} (hcost : CouplingCostBound (fun t => (μ t:Measure X)) C) :
    DynamicActionBound (fun t => (μ t:Measure X)) C := by
  intro s t
  obtain ⟨q,hq,hqb⟩ := hcost s t
  have hp : IsProbabilityMeasure (q.map Prod.fst) := by rw [hq.1]; infer_instance
  let := Measure.isProbabilityMeasure_of_map (μ := q) measurable_fst.aemeasurable
  obtain ⟨π,h0,h1,hA⟩ := hcd.lift_coupling q (by rw [hq.1]; exact hac s)
    (by rw [hq.2]; exact hac t)
  have hpπ : IsProbabilityMeasure (π.map (fun γ => γ timeZero)) := by
    change IsProbabilityMeasure (interpolation π timeZero)
    rw [h0,hq.1]
    infer_instance
  let := Measure.isProbabilityMeasure_of_map (μ := π)
    (continuous_eval_const timeZero).measurable.aemeasurable
  exact ⟨π,inferInstance,h0.trans hq.1,h1.trans hq.2,hA.trans hqb⟩

lemma exists_proper_testPlan_superposition (m : Measure X)
    (μ : Time → ProbabilityMeasure X) (hμ : Continuous μ)
    {C : ℝ} (hC : 0 ≤ C) (h : DynamicActionBound (fun t => (μ t:Measure X)) C)
    (hcomp : ∃ L : ℝ≥0, ∀ t : Time,(μ t:Measure X) ≤ (L:ℝ≥0∞) • m) :
    ∃ π : Measure (Curve X), IsTestPlan m π ∧
      (∀ t : Time,π.map (fun γ => γ t) = (μ t:Measure X)) ∧
      (∫⁻ γ,∫⁻ t in Icc (0:ℝ) 1,(metricSpeed γ t)^2 ∂volume ∂π) ≤ ENNReal.ofReal C := by
  obtain ⟨π,hmarg,_hA,hAC,hS⟩ := exists_superposition_proper μ hμ hC h
  refine ⟨π,⟨inferInstance,?_,hAC,hS.trans_lt ENNReal.ofReal_lt_top⟩,hmarg,hS⟩
  obtain ⟨L,hL⟩ := hcomp
  exact ⟨L,fun t => by rw [hmarg t]; exact hL t⟩

lemma CurvatureDimension.testPlan_of_cost_proper {m : Measure X} {K N : ℝ}
    (hcd : CurvatureDimension m K N)
    (μ : Time → ProbabilityMeasure X) (hμ : Continuous μ)
    {C : ℝ} (hC : 0 ≤ C) (hcost : CouplingCostBound (fun t => (μ t:Measure X)) C)
    (hcomp : ∃ L : ℝ≥0, ∀ t : Time,(μ t:Measure X) ≤ (L:ℝ≥0∞) • m) :
    ∃ π : Measure (Curve X), IsTestPlan m π ∧
      (∀ t : Time,π.map (fun γ => γ t) = (μ t:Measure X)) ∧
      (∫⁻ γ,∫⁻ t in Icc (0:ℝ) 1,(metricSpeed γ t)^2 ∂volume ∂π) ≤ ENNReal.ofReal C := by
  apply exists_proper_testPlan_superposition m μ hμ hC _ hcomp
  apply hcd.dynamicActionBound_proper μ _ hcost
  obtain ⟨L,hL⟩ := hcomp
  intro t
  exact (Measure.absolutelyContinuous_of_le (hL t)).trans Measure.smul_absolutelyContinuous
end WeakHessian

namespace WeakHessian
open WeakHessianFunctional WeakHessianTransport MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X} [IsProbabilityMeasure m]

lemma prox_linearDensity_coupling_forward {u v D : Lp ℝ 2 m} {t : ℝ}
    (h : RelaxedProx u t v D) (hmass : ∫ x,u x ∂m = 0) {ε B a b : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hεB : ε*B < 1)
    (hu : ∀ᵐ x ∂m, |u x| ≤ B) (hv : ∀ᵐ x ∂m, |v x| ≤ B)
    (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) (hab : a ≤ b) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = densityMeasure m (linearDensity ε u v b) ∧
      q.map Prod.snd = densityMeasure m (linearDensity ε u v a) ∧
      (∫⁻ p,(edist p.1 p.2)^2 ∂q) ≤
        ENNReal.ofReal (ε^2/(1-ε*B)*(t^2*‖D‖)^2*(b-a)^2) := by
  have hi (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : a+(b-a)*r ∈ Icc (0:ℝ) 1 := by
    constructor
    · have := mul_nonneg (sub_nonneg.mpr hab) hr.1; linarith [ha.1]
    · have := mul_le_mul_of_nonneg_left hr.2 (sub_nonneg.mpr hab); nlinarith [hb.2]
  have hα : 0 < 1-ε*B := sub_pos.mpr hεB
  have hpos (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
      ∀ᵐ x ∂m,0 ≤ linearDensity ε u v (a+(b-a)*r) x :=
    (linearDensity_bounds hε hB (hi r hr) hu hv).mono fun _ hx => hα.le.trans hx.1
  have hv0 := h.mass.trans hmass
  obtain ⟨q,hq,hq0,hq1,hqb⟩ := proper_dual_density_coupling_bound m
    (ρ := fun r => linearDensity ε u v (a+(b-a)*r))
    (A := fun _ => (-(ε*(b-a))) • (u-v))
    (M := (-(ε*(b-a)))^2/(1-ε*B)*(t^2*‖D‖)^2/2)
    hα ((continuous_linearDensity ε u v).comp (by fun_prop)).continuousOn hpos
    (fun r _ => linearDensity_mass ε u v hmass hv0 _)
    (fun r hr => (linearDensity_bounds hε hB (hi r (Ico_subset_Icc_self hr)) hu hv).mono fun _ hx => hx.1)
    (fun _ _ f hf => h.young hf hα)
    (fun r _ => by
      have H := (linearDensity_affine_deriv ε u v a (b-a) r).hasDerivWithinAt (s := Ici r)
      have he : (-(ε*(b-a))) • (u-v) = (ε*(b-a)) • (v-u) := by
        rw [neg_smul,smul_sub,smul_sub]
        abel
      rw [he]
      exact H)
  refine ⟨q,hq,?_,?_,?_⟩
  · convert hq0 using 2
    congr 2
    ring
  · simpa only [mul_zero,add_zero] using hq1
  · apply hqb.trans_eq
    congr 1
    ring

lemma prox_linearDensity_coupling_cost {u v D : Lp ℝ 2 m} {t : ℝ}
    (h : RelaxedProx u t v D) (hmass : ∫ x,u x ∂m = 0) {ε B : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B) (hεB : ε*B < 1)
    (hu : ∀ᵐ x ∂m, |u x| ≤ B) (hv : ∀ᵐ x ∂m, |v x| ≤ B) :
    CouplingCostBound (fun r : Time => densityMeasure m (linearDensity ε u v r))
      (ε^2/(1-ε*B)*(t^2*‖D‖)^2) := by
  intro s r
  rcases le_total (s:ℝ) (r:ℝ) with hsr | hrs
  · obtain ⟨q,hq,hq0,hq1,hqb⟩ := prox_linearDensity_coupling_forward h hmass hε hB hεB hu hv s.2 r.2 hsr
    refine ⟨q.map Prod.swap,⟨?_,?_⟩,?_⟩
    · rw [Measure.map_map measurable_fst measurable_swap]
      simpa only [Function.comp_def,Prod.fst_swap] using hq1
    · rw [Measure.map_map measurable_snd measurable_swap]
      simpa only [Function.comp_def,Prod.snd_swap] using hq0
    · rw [QuadraticTransportCost,lintegral_map
        ((continuous_fst.edist continuous_snd).measurable.pow_const 2) measurable_swap]
      simp only [Prod.fst_swap,Prod.snd_swap]
      simp_rw [edist_comm]
      convert hqb using 1
      congr 1
      change _ * |(s:ℝ)-(r:ℝ)|^2 = _
      rw [sq_abs]
      ring
  · obtain ⟨q,hq,hq0,hq1,hqb⟩ := prox_linearDensity_coupling_forward h hmass hε hB hεB hu hv r.2 s.2 hrs
    refine ⟨q,⟨hq0,hq1⟩,?_⟩
    change (∫⁻ p,(edist p.1 p.2)^2 ∂q) ≤ _
    convert hqb using 1
    congr 1
    change _ * |(s:ℝ)-(r:ℝ)|^2 = _
    rw [sq_abs]

end WeakHessian

end
end InlinedFile0

end OAI
