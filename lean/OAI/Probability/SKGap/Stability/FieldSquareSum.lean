import Mathlib
import OAI.Probability.SKGap.Localization.LinearObservable

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace SKGapCutoff

lemma field_square_sum_le {n : ℕ} (J : Interaction n) (x : Spin n)
    {K : ℝ} (_hK : 0 ≤ K)
    (hJ : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ ≤ K) :
    ∑ i, field J x i^2 ≤ K^2*(n:ℝ) := by
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J
  let v : EuclideanSpace ℝ (Fin n) := (WithLp.equiv 2 _).symm (spin x)
  have hv : ‖v‖^2 = (n:ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact overlap_coeff_norm_sq x
  have hh : ‖A v‖ ≤ K*‖v‖ := (A.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
  rw [mul_pow, hv, EuclideanSpace.real_norm_sq_eq] at hs
  exact hs

lemma one_sub_tanh_half (a : ℝ) :
    (1-Real.tanh a)/2 = 1/(1+Real.exp (2*a)) := by
  have hh := exp_two_mul_one_sub_tanh a
  have he := Real.exp_pos (2*a)
  apply (eq_div_iff (by positivity : (1+Real.exp (2*a)) ≠ 0)).mpr
  nlinarith

lemma one_add_tanh_half (a : ℝ) :
    (1+Real.tanh a)/2 = 1/(1+Real.exp (-2*a)) := by
  simpa only [Real.tanh_neg, sub_neg_eq_add, mul_neg, neg_mul] using one_sub_tanh_half (-a)

lemma siteRefresh_diagonal_lower {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    1/(1+Real.exp (2*|field J x i|)) ≤
      siteRefresh J i (fun z => if z=x then 1 else 0) x := by
  have htrue : replace x i true = x ↔ x i = true := by
    constructor
    · intro h; simpa using (congrFun h i).symm
    · intro h; simpa only [h] using replace_self x i
  have hfalse : replace x i false = x ↔ x i = false := by
    constructor
    · intro h; simpa using (congrFun h i).symm
    · intro h; simpa only [h] using replace_self x i
  simp only [siteRefresh, htrue, hfalse, mean]
  cases x i <;> simp only [ Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, mul_zero, mul_one, zero_add, add_zero]
  · rw [one_sub_tanh_half]
    apply one_div_le_one_div_of_le (by positivity)
    apply add_le_add le_rfl
    apply Real.exp_le_exp.mpr
    linarith [le_abs_self (field J x i)]
  · rw [one_add_tanh_half]
    apply one_div_le_one_div_of_le (by positivity)
    apply add_le_add le_rfl
    apply Real.exp_le_exp.mpr
    linarith [neg_le_abs (field J x i)]

lemma logistic_quadratic_lower {a L : ℝ} (hL : 0 < L) :
    (1-a^2/L^2)/(1+Real.exp (2*L)) ≤ 1/(1+Real.exp (2*|a|)) := by
  by_cases ha : |a| ≤ L
  · calc
      _ ≤ 1/(1+Real.exp (2*L)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : 0 ≤ a^2/L^2 := by positivity
        linarith
      _ ≤ _ := by
        apply one_div_le_one_div_of_le (by positivity)
        apply add_le_add le_rfl
        apply Real.exp_le_exp.mpr
        linarith
  · have ha2 : L^2 ≤ a^2 := by nlinarith [sq_abs a, abs_nonneg a, le_of_not_ge ha]
    have hratio : 1 ≤ a^2/L^2 := (one_le_div (sq_pos_of_pos hL)).mpr ha2
    exact (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)).trans (by positivity)

lemma attempted_holding_lower {n : ℕ} (hn : 0 < n) (J : Interaction n)
    {K : ℝ} (hK : 0 < K)
    (hJ : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ ≤ K) (x : Spin n) :
    1/(2*(1+Real.exp (2*(Real.sqrt 2*K)))) ≤ discreteKernel J 1 x x := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hL : 0 < Real.sqrt 2*K := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hK
  have hL2 : (Real.sqrt 2*K)^2 = 2*K^2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hsum := field_square_sum_le J x hK.le hJ
  have hs : (∑ i, (1-field J x i^2/(Real.sqrt 2*K)^2)/(1+Real.exp (2*(Real.sqrt 2*K)))) ≤
      ∑ i, siteRefresh J i (fun z => if z=x then 1 else 0) x := by
    apply Finset.sum_le_sum
    intro i _
    exact (logistic_quadratic_lower hL).trans (siteRefresh_diagonal_lower J x i)
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hL2] at hs
  have hf : (∑ i, field J x i^2)/(2*K^2) ≤ (n:ℝ)/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*K^2)).mpr
    nlinarith
  change _ ≤ (attemptLM J ^ 1) (fun z => if z=x then 1 else 0) x
  rw [pow_one, attempt_apply_of_pos hn]
  apply (le_div_iff₀ hnR).mpr
  calc
    _ = ((n:ℝ)/2)/(1+Real.exp (2*(Real.sqrt 2*K))) := by field_simp
    _ ≤ ((n:ℝ)-(∑ i, field J x i^2)/(2*K^2))/(1+Real.exp (2*(Real.sqrt 2*K))) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ _ := hs

end SKGapCutoff

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology

end

end OAI
