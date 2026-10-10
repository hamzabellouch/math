import Mathlib
import OAI.Probability.SKGap.Localization.JumpEnergy
import OAI.Probability.SKGap.Stability.FieldSquareSum

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
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory ContinuousLinearMap
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter
open scoped BigOperators Topology
namespace SKGapCutoff

lemma exp_abs_le_sum (z : ℝ) : Real.exp |z| ≤ Real.exp z + Real.exp (-z) := by
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    linarith [Real.exp_pos (-z)]
  · rw [abs_of_nonpos hz]
    linarith [Real.exp_pos z]

lemma indicator_max_le_exp {n : ℕ} (u c : Fin n → ℝ) {θ H m : ℝ}
    (hθ : 0 ≤ θ) (hc : ∀ i, |c i| ≤ m) :
    (if ∃ i, H < |u i| then (1:ℝ) else 0) ≤
      Real.exp (-θ*(H-m)) * ∑ i, (Real.exp (θ*(u i-c i)) + Real.exp (-θ*(u i-c i))) := by
  classical
  by_cases hu : ∃ i, H < |u i|
  · simp only [hu, ↓reduceIte]
    obtain ⟨i, hi⟩ := hu
    have htri : H-m ≤ |u i-c i| := by
      have hh : |u i| ≤ |u i-c i|+|c i| := by
        simpa only [sub_add_cancel] using abs_add_le (u i-c i) (c i)
      linarith [hc i]
    have hs : Real.exp (θ*|u i-c i|) ≤
        ∑ j, (Real.exp (θ*(u j-c j)) + Real.exp (-θ*(u j-c j))) := by
      have hh := exp_abs_le_sum (θ*(u i-c i))
      rw [abs_mul, abs_of_nonneg hθ] at hh
      have hh' : Real.exp (θ*|u i-c i|) ≤
          Real.exp (θ*(u i-c i))+Real.exp (-θ*(u i-c i)) := by
        simpa only [neg_mul] using hh
      exact hh'.trans (Finset.single_le_sum (f := fun j =>
        Real.exp (θ*(u j-c j))+Real.exp (-θ*(u j-c j)))
        (fun j _ => by positivity) (Finset.mem_univ i))
    calc
      1 ≤ Real.exp (-θ*(H-m))*Real.exp (θ*|u i-c i|) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        have hh := mul_le_mul_of_nonneg_left htri hθ
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
  · simp only [hu, ↓reduceIte]
    positivity

lemma semigroup_max_tail {n : ℕ} (J : Interaction n) (f : Fin n → Observables n)
    {t θ H m C : ℝ} (ht : 0 ≤ t) (hθ : 0 ≤ θ) (x : Spin n)
    (hmean : ∀ i, |semigroup J t (f i) x| ≤ m)
    (hmgf : ∀ i, ∀ σ ∈ ({-1,1}:Set ℝ),
      semigroup J t (fun y => Real.exp (σ*θ*(f i y-semigroup J t (f i) x))) x ≤ C) :
    semigroup J t (fun y => if ∃ i, H < |f i y| then (1:ℝ) else 0) x ≤
      2*(n:ℝ)*C*Real.exp (-θ*(H-m)) := by
  classical
  have hh := semigroup_mono J t ht (fun y =>
    indicator_max_le_exp (fun i => f i y) (fun i => semigroup J t (f i) x) (H := H) hθ hmean) x
  have he : (fun y => Real.exp (-θ*(H-m))*∑ i,
      (Real.exp (θ*(f i y-semigroup J t (f i) x)) +
       Real.exp (-θ*(f i y-semigroup J t (f i) x)))) =
      Real.exp (-θ*(H-m)) • ∑ i : Fin n,
        ((fun y => Real.exp (θ*(f i y-semigroup J t (f i) x))) +
         (fun y => Real.exp (-θ*(f i y-semigroup J t (f i) x)))) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.add_apply]
  rw [he, map_smul, map_sum] at hh
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, map_add, Pi.add_apply] at hh
  have hib : ∀ i : Fin n,
      semigroup J t (fun y => Real.exp (θ*(f i y-semigroup J t (f i) x))) x +
      semigroup J t (fun y => Real.exp (-θ*(f i y-semigroup J t (f i) x))) x ≤ 2*C := by
    intro i
    have hpos := hmgf i 1 (by simp)
    have hneg := hmgf i (-1) (by simp)
    simp only [one_mul, neg_one_mul] at hpos hneg
    linarith
  calc
    _ ≤ _ := hh
    _ ≤ Real.exp (-θ*(H-m))*∑ _i : Fin n, 2*C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hib i)) (Real.exp_pos _).le
    _ = _ := by simp; ring

lemma jumpWeight_lower_from_field {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n)
    {H : ℝ} (hH : |field J x i| ≤ H) :
    2/(1+Real.exp (2*H)) ≤ 1-mean J x i*spin x i := by
  have hpos : 1/(1+Real.exp (2*H)) ≤ 1/(1+Real.exp (2*field J x i)) := by
    apply one_div_le_one_div_of_le (by positivity)
    apply add_le_add le_rfl
    exact Real.exp_le_exp.mpr (by linarith [le_abs_self (field J x i)])
  have hneg : 1/(1+Real.exp (2*H)) ≤ 1/(1+Real.exp (-2*field J x i)) := by
    apply one_div_le_one_div_of_le (by positivity)
    apply add_le_add le_rfl
    exact Real.exp_le_exp.mpr (by linarith [neg_le_abs (field J x i)])
  rw [← one_sub_tanh_half (field J x i)] at hpos
  rw [← one_add_tanh_half (field J x i)] at hneg
  simp only [div_eq_mul_inv, one_mul] at hpos hneg ⊢
  cases hs : x i <;> simp only [spin, hs, Bool.false_eq_true, ↓reduceIte,
    mean, mul_neg_one, mul_one] <;> linarith

end SKGapCutoff

open MeasureTheory Filter
open scoped BigOperators Topology

end

end OAI
