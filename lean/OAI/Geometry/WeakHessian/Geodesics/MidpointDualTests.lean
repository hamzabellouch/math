import Mathlib
import OAI.Geometry.WeakHessian.Transport.BoundedHopfMap

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X]

def midpointDualTest (o : X) (R : ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => max (R^2-dist x o^2) 0/2) (by fun_prop) (R^2/2) (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right (max_le (by nlinarith [sq_nonneg (dist x o)]) (sq_nonneg R)) (by norm_num))

@[simp] lemma midpointDualTest_apply (o : X) (R : ℝ) (x : X) :
    midpointDualTest o R x = max (R^2-dist x o^2) 0/2 := rfl

lemma midpointDualTest_nonneg (o : X) (R : ℝ) (x : X) : 0 ≤ midpointDualTest o R x := by
  simp only [midpointDualTest_apply]; positivity

lemma midpointDualTest_le (o : X) (R : ℝ) (x : X) : midpointDualTest o R x ≤ R^2/2 := by
  simp only [midpointDualTest_apply]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
  exact max_le (by nlinarith [sq_nonneg (dist x o)]) (sq_nonneg R)

lemma midpointDualTest_compact [ProperSpace X] (o : X) {R : ℝ} (hR : 0 ≤ R) :
    HasCompactSupport (midpointDualTest o R : X → ℝ) := by
  apply HasCompactSupport.intro' (isCompact_closedBall o R) Metric.isClosed_closedBall
  intro x hx
  have hdist : R ≤ dist x o := le_of_lt (lt_of_not_ge hx)
  simp only [midpointDualTest_apply]
  rw [max_eq_right (by nlinarith [dist_nonneg (x := x) (y := o)] : R^2-dist x o^2 ≤ 0),zero_div]

lemma midpointDualTest_hopf_one [ProperSpace X] (o : X) (R : ℝ) :
    boundedHopfMap (midpointDualTest o R) 1 o = R^2/2 := by
  rw [boundedHopfMap_apply_pos _ zero_lt_one]
  apply le_antisymm
  · have H := hopfLax_le_self (midpointDualTest_nonneg o R) zero_lt_one o
    simpa only [midpointDualTest_apply,dist_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),sub_zero,max_eq_left (sq_nonneg R)] using H
  · apply le_csInf ⟨hopfObjective (midpointDualTest o R) 1 o o,mem_range_self o⟩
    rintro v ⟨x,rfl⟩
    dsimp only [hopfObjective]
    rw [midpointDualTest_apply,dist_comm o x]
    have H := le_max_left (R^2-dist x o^2) 0
    nlinarith only [H]

lemma midpointDualTest_sum_le (x₀ x₁ z : X) {R : ℝ} (hR : dist x₀ x₁ ≤ R) :
    midpointDualTest x₀ R z+midpointDualTest x₁ R z ≤ R^2-dist x₀ x₁^2/4 := by
  have hRn : 0 ≤ R := dist_nonneg.trans hR
  have hDsq : dist x₀ x₁^2 ≤ R^2 := (sq_le_sq₀ dist_nonneg hRn).mpr hR
  have htri : dist x₀ x₁ ≤ dist z x₀+dist z x₁ := by
    simpa only [dist_comm x₀ z] using dist_triangle x₀ z x₁
  have hsq : dist x₀ x₁^2 ≤ 2*(dist z x₀^2+dist z x₁^2) := by
    nlinarith [sq_nonneg (dist z x₀-dist z x₁),dist_nonneg (x := z) (y := x₀),dist_nonneg (x := z) (y := x₁),dist_nonneg (x := x₀) (y := x₁)]
  simp only [midpointDualTest_apply]
  rcases le_total (R^2-dist z x₀^2) 0 with h₀ | h₀
  · rw [max_eq_right h₀]
    have H := max_le (by nlinarith [sq_nonneg (dist z x₁)] : R^2-dist z x₁^2 ≤ R^2) (sq_nonneg R)
    nlinarith
  · rw [max_eq_left h₀]
    rcases le_total (R^2-dist z x₁^2) 0 with h₁ | h₁
    · rw [max_eq_right h₁]
      nlinarith [sq_nonneg (dist z x₀)]
    · rw [max_eq_left h₁]
      nlinarith only [hsq]

section Laws
variable [ProperSpace X] [MeasurableSpace X] [BorelSpace X]

lemma hopf_integral_terminal_lower (f : X →ᵇ ℝ) {D : ℝ≥0}
    (hD : LipschitzWith D (boundedHopfMap f 1)) (μ : ProbabilityMeasure X)
    (o : X) {r q : ℝ} (hs : ∀ᵐ x ∂(μ:Measure X),dist x o ≤ r) (hq : 0 < q) :
    boundedHopfMap f 1 o-(D:ℝ)*r-2*‖f‖*q ≤ ∫ x,boundedHopfMap f (q+1) x ∂(μ:Measure X) := by
  have htime := (boundedHopfMap_time_lipschitz f zero_lt_one).dist_le_mul (q+1) (by change (1:ℝ) ≤ q+1; linarith)
    1 (by simp : (1:ℝ) ∈ Ici 1)
  have htime' : dist (boundedHopfMap f (q+1)) (boundedHopfMap f 1) ≤ 2*‖f‖*q := by
    change dist (boundedHopfMap f (q+1)) (boundedHopfMap f 1) ≤ (2*‖f‖/1)*dist (q+1) 1 at htime
    simpa only [div_one,Real.dist_eq,add_sub_cancel_right,abs_of_pos hq] using htime
  have hlower : ∀ᵐ x ∂(μ:Measure X),boundedHopfMap f 1 o-(D:ℝ)*r-2*‖f‖*q ≤ boundedHopfMap f (q+1) x := by
    filter_upwards [hs] with x hx
    have HD := hD.dist_le_mul x o
    have HT := (BoundedContinuousFunction.dist_coe_le_dist (f := boundedHopfMap f (q+1)) (g := boundedHopfMap f 1) x).trans htime'
    have HB := mul_le_mul_of_nonneg_left hx D.property
    rw [Real.dist_eq] at HD HT
    have HDlo := (abs_le.mp HD).1
    have HTlo := (abs_le.mp HT).1
    change -(↑D*dist x o) ≤ boundedHopfMap f 1 x-boundedHopfMap f 1 o at HDlo
    change -(2*‖f‖*q) ≤ boundedHopfMap f (q+1) x-boundedHopfMap f 1 x at HTlo
    calc
      _ ≤ boundedHopfMap f 1 o-(D:ℝ)*dist x o-2*‖f‖*q :=
        sub_le_sub_right (sub_le_sub_left HB _) _
      _ ≤ boundedHopfMap f 1 x-2*‖f‖*q := sub_le_sub_right (by linarith only [HDlo]) _
      _ ≤ boundedHopfMap f (q+1) x := by linarith only [HTlo]
  have H := integral_mono_ae (integrable_const _) ((boundedHopfMap f (q+1)).integrable (μ := (μ:Measure X))) hlower
  simpa only [Pi.add_apply,integral_const,probReal_univ,one_smul] using H

lemma midpoint_dual_lower (x₀ x₁ : X) {R : ℝ} (hR : dist x₀ x₁ ≤ R)
    (μ₀ μ₁ ν : ProbabilityMeasure X) {D₀ D₁ : ℝ≥0}
    (hD₀ : LipschitzWith D₀ (boundedHopfMap (midpointDualTest x₀ R) 1))
    (hD₁ : LipschitzWith D₁ (boundedHopfMap (midpointDualTest x₁ R) 1))
    {r₀ r₁ q : ℝ} (hs₀ : ∀ᵐ x ∂(μ₀:Measure X),dist x x₀ ≤ r₀)
    (hs₁ : ∀ᵐ x ∂(μ₁:Measure X),dist x x₁ ≤ r₁) (hq : 0 < q) :
    dist x₀ x₁^2/4-(D₀:ℝ)*r₀-(D₁:ℝ)*r₁-
      2*(‖midpointDualTest x₀ R‖+‖midpointDualTest x₁ R‖)*q ≤
      ((∫ x,boundedHopfMap (midpointDualTest x₀ R) (q+1) x ∂(μ₀:Measure X))-
        (∫ x,boundedHopfMap (midpointDualTest x₀ R) q x ∂(ν:Measure X)))+
      ((∫ x,boundedHopfMap (midpointDualTest x₁ R) (q+1) x ∂(μ₁:Measure X))-
        (∫ x,boundedHopfMap (midpointDualTest x₁ R) q x ∂(ν:Measure X))) := by
  have H₀ := hopf_integral_terminal_lower _ hD₀ μ₀ x₀ hs₀ hq
  have H₁ := hopf_integral_terminal_lower _ hD₁ μ₁ x₁ hs₁ hq
  rw [midpointDualTest_hopf_one] at H₀ H₁
  have Hinit : (∫ x,boundedHopfMap (midpointDualTest x₀ R) q x ∂(ν:Measure X))+
      (∫ x,boundedHopfMap (midpointDualTest x₁ R) q x ∂(ν:Measure X)) ≤ R^2-dist x₀ x₁^2/4 := by
    rw [← integral_add (BoundedContinuousFunction.integrable (ν:Measure X) _) (BoundedContinuousFunction.integrable (ν:Measure X) _)]
    have hpoint (z : X) : boundedHopfMap (midpointDualTest x₀ R) q z+
        boundedHopfMap (midpointDualTest x₁ R) q z ≤ R^2-dist x₀ x₁^2/4 := by
      rw [boundedHopfMap_apply_pos _ hq,boundedHopfMap_apply_pos _ hq]
      exact (add_le_add (hopfLax_le_self (midpointDualTest_nonneg x₀ R) hq z)
        (hopfLax_le_self (midpointDualTest_nonneg x₁ R) hq z)).trans (midpointDualTest_sum_le x₀ x₁ z hR)
    have H := integral_mono_ae (Integrable.add
      ((boundedHopfMap (midpointDualTest x₀ R) q).integrable (μ := (ν:Measure X)))
      ((boundedHopfMap (midpointDualTest x₁ R) q).integrable (μ := (ν:Measure X))))
      (integrable_const (R^2-dist x₀ x₁^2/4)) (ae_of_all (ν:Measure X) hpoint)
    simpa only [Pi.add_apply,integral_const,probReal_univ,one_smul] using H
  linarith only [H₀,H₁,Hinit]
end Laws
end WeakHessian

end
end

end OAI
