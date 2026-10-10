import Mathlib
import OAI.Geometry.WeakHessian.Entropy.FiniteEntropyBoundedSupported
import OAI.Geometry.WeakHessian.Transport.PlanIncrement

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma exists_small_ball_law (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {r : ℝ} (hr : 0 < r) :
    ∃ μ : ProbabilityMeasure X,∃ B : ℝ≥0,0 < B ∧
      (μ:Measure X) ≤ (B : ℝ≥0∞) • m ∧ (∀ᵐ x ∂(μ:Measure X),dist x o ≤ r) := by
  let S := Metric.ball o r
  have hS : MeasurableSet S := Metric.isOpen_ball.measurableSet
  have hSp : m S ≠ 0 := (hfull S Metric.isOpen_ball ⟨o,Metric.mem_ball_self hr⟩).ne'
  have hSt : m S ≠ ∞ := (hfin S Metric.isBounded_ball).ne
  let ν := (m S)⁻¹ • m.restrict S
  have hp : IsProbabilityMeasure ν := ⟨by
    simp only [ν,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
    exact ENNReal.inv_mul_cancel hSp hSt⟩
  let μ : ProbabilityMeasure X := ⟨ν,hp⟩
  refine ⟨μ,((m S)⁻¹).toNNReal,?_,?_,?_⟩
  · exact ENNReal.toNNReal_pos (by simpa only [ne_eq,ENNReal.inv_eq_zero] using hSt)
      (by simpa only [ne_eq,ENNReal.inv_eq_top] using hSp)
  · rw [ENNReal.coe_toNNReal (by simpa only [ne_eq,ENNReal.inv_eq_top] using hSp)]
    change (m S)⁻¹ • m.restrict S ≤ (m S)⁻¹ • m
    gcongr
    exact Measure.restrict_le_self
  · exact (Measure.ae_smul_measure (ae_restrict_mem hS) ((m S)⁻¹)).mono fun x hx => hx.le

omit [CompleteSpace X] in
lemma CurvatureDimension.exists_plan_leg {K N : ℝ} (hN : 1 < N)
    (hCD : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m)
    (μ₀ μ₁ : ProbabilityMeasure X) (x₀ x₁ : X) {r : ℝ} (hr : 0 ≤ r)
    (hs₀ : ∀ᵐ x ∂(μ₀:Measure X),dist x x₀ ≤ r)
    (hs₁ : ∀ᵐ x ∂(μ₁:Measure X),dist x x₁ ≤ r)
    {B₀ B₁ : ℝ≥0} (hB₀ : 0 < B₀) (hB₁ : 0 < B₁)
    (hb₀ : (μ₀:Measure X) ≤ (B₀:ℝ≥0∞) • m)
    (hb₁ : (μ₁:Measure X) ≤ (B₁:ℝ≥0∞) • m) :
    ∃ π : Measure (Curve X),∃ C : ℝ≥0,0 < C ∧ IsTestPlan m π ∧ BoundedTracks π ∧
      (∀ᵐ γ ∂π,IsGeodesic γ) ∧
      π.map (fun γ => γ timeZero) = (μ₀:Measure X) ∧
      π.map (fun γ => γ timeOne) = (μ₁:Measure X) ∧
      (∀ t : Time,π.map (fun γ => γ t) ≤ (C:ℝ≥0∞) • m) ∧
      (∀ᵐ γ ∂π,dist (γ timeZero) x₀ ≤ r ∧ dist (γ timeOne) x₁ ≤ r ∧
        dist (γ timeZero) (γ timeOne) ≤ dist x₀ x₁+2*r) ∧
      planKineticCost π ≤ (dist x₀ x₁+2*r)^2 := by
  let R : ℝ≥0 := ⟨dist x₀ x₁+r+1,by positivity⟩
  let B : ℝ≥0 := B₀+B₁
  have hB : 0 < B := add_pos hB₀ hB₁
  have hb0 : (μ₀:Measure X) ≤ (B:ℝ≥0∞) • m := hb₀.trans (by
    gcongr; exact le_add_of_nonneg_right (show 0 ≤ B₁ from zero_le))
  have hb1 : (μ₁:Measure X) ≤ (B:ℝ≥0∞) • m := hb₁.trans (by
    gcongr; exact le_add_of_nonneg_left (show 0 ≤ B₀ from zero_le))
  have hS0 : (μ₀:Measure X) (Metric.closedBall x₀ (R:ℝ))ᶜ = 0 := ae_iff.mp
    (hs₀.mono fun x hx => by change dist x x₀ ≤ dist x₀ x₁+r+1; linarith [dist_nonneg (x := x₀) (y := x₁)])
  have hS1 : (μ₁:Measure X) (Metric.closedBall x₀ (R:ℝ))ᶜ = 0 := ae_iff.mp
    (hs₁.mono fun x hx => by
      change dist x x₀ ≤ dist x₀ x₁+r+1
      have H := dist_triangle x x₁ x₀
      rw [dist_comm x₁ x₀] at H; linarith)
  obtain ⟨π,hπ,hbt,hg,ho,_,_,hcap⟩ := hCD.exists_entropy_testPlan hN hfin μ₀ μ₁ x₀ R
    hS0 hS1 (by exact_mod_cast hB.ne') ENNReal.coe_ne_top hb0 hb1
  let C : ℝ≥0 := B*(Real.exp (4*compressionRate K N*R)).toNNReal
  have hC : 0 < C := mul_pos hB (Real.toNNReal_pos.mpr (Real.exp_pos _))
  have h0 : (π:Measure (Curve X)).map (fun γ => γ timeZero) = (μ₀:Measure X) := by
    simpa only [endpointCoupling,Measure.map_map measurable_fst
      ((continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable),Function.comp_def]
      using ho.1.1
  have h1 : (π:Measure (Curve X)).map (fun γ => γ timeOne) = (μ₁:Measure X) := by
    simpa only [endpointCoupling,Measure.map_map measurable_snd
      ((continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable),Function.comp_def]
      using ho.1.2
  have ht : ∀ᵐ γ ∂(π:Measure (Curve X)),dist (γ timeZero) x₀ ≤ r ∧
      dist (γ timeOne) x₁ ≤ r ∧ dist (γ timeZero) (γ timeOne) ≤ dist x₀ x₁+2*r := by
    have H0 := ae_of_ae_map (μ := (π:Measure (Curve X))) (f := fun γ => γ timeZero)
      (continuous_eval_const timeZero).measurable.aemeasurable (h0.symm ▸ hs₀)
    have H1 := ae_of_ae_map (μ := (π:Measure (Curve X))) (f := fun γ => γ timeOne)
      (continuous_eval_const timeOne).measurable.aemeasurable (h1.symm ▸ hs₁)
    filter_upwards [H0,H1] with γ hγ0 hγ1
    refine ⟨hγ0,hγ1,?_⟩
    have H := dist_triangle (γ timeZero) x₀ (γ timeOne)
    have H' := dist_triangle x₀ x₁ (γ timeOne)
    rw [dist_comm x₁ (γ timeOne)] at H'
    linarith
  refine ⟨π,C,hC,hπ,hbt,hg,h0,h1,?_,ht,?_⟩
  · intro t
    simpa only [C,interpolation,ENNReal.coe_mul,ENNReal.ofReal] using hcap t
  · have hi : Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) (π:Measure (Curve X)) :=
      Integrable.of_bound (by fun_prop) ((dist x₀ x₁+2*r)^2) (ht.mono fun γ hγ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ dist_nonneg hγ.2.2 2)
    have H := integral_mono_ae hi (integrable_const ((dist x₀ x₁+2*r)^2))
      (ht.mono fun γ hγ => pow_le_pow_left₀ dist_nonneg hγ.2.2 2)
    simpa only [planKineticCost,integral_const,probReal_univ,one_smul] using H

end WeakHessian

end
end

end OAI
