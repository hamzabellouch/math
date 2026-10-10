import Mathlib
import OAI.Probability.SKGap.Matrix.DoublePlantLogNorm

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
namespace SKGapCutoff

lemma replicaOverlap_comm {n : ℕ} (x y : Spin n) : replicaOverlap x y = replicaOverlap y x := by
  simp only [replicaOverlap, mul_comm]

lemma doublePlantWeight_comm {n : ℕ} (β : ℝ) (x y : Spin n) :
    doublePlantWeight β x y = doublePlantWeight β y x := by
  simp only [doublePlantWeight, doublePlantLogNorm, replicaOverlap_comm x y]

lemma doublePlantWeight_marginal (β : ℝ) {n : ℕ} (hn : 0 < n) (x : Spin n) :
    ∑ y : Spin n, doublePlantWeight β x y = 1/(2:ℝ)^n := by
  have hs := sum_replicaOverlap x (fun z => Real.exp (β^2*z^2/(2*n)))
  let S := ∑ y : Spin n, Real.exp (β^2*magnetization y^2/(2*n))
  have hS : 0 < S := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  simp_rw [doublePlantWeight_eq_overlap_tilt β hn]
  rw [← Finset.sum_div, hs]
  simp_rw [sum_replicaOverlap _ (fun z => Real.exp (β^2*z^2/(2*n)))]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change S/((Fintype.card (Spin n):ℝ)*S) = _
  rw [card_spin, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

lemma doublePlantWeight_right_marginal (β : ℝ) {n : ℕ} (hn : 0 < n) (y : Spin n) :
    ∑ x : Spin n, doublePlantWeight β x y = 1/(2:ℝ)^n := by
  simp_rw [doublePlantWeight_comm β _ y]
  exact doublePlantWeight_marginal β hn y

lemma doublePlantWeight_magnetization_tail (β q ε : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hε : 0 < ε) {n : ℕ} (hn : 0 < n) :
    (∑ x : Spin n, ∑ y : Spin n, if ε*n < |magnetization x| then
      doublePlantWeight β x y else 0) ≤
        Real.exp (-(q*ε^2*n/2))*(Real.sqrt (1-q))⁻¹ := by
  have he (x : Spin n) : (∑ y : Spin n, if ε*n < |magnetization x| then
      doublePlantWeight β x y else 0) =
      (if ε*n < |magnetization x| then (1:ℝ) else 0)/(2:ℝ)^n := by
    split_ifs <;> simp [doublePlantWeight_marginal β hn]
  simp_rw [he]
  rw [← Finset.sum_div]
  simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul, zero_div,
    Real.exp_zero, sub_zero] using sign_square_tail_le 0 q ε (by simpa using hq0) hq1 hε hn

lemma doublePlantWeight_right_magnetization_tail (β q ε : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hε : 0 < ε) {n : ℕ} (hn : 0 < n) :
    (∑ x : Spin n, ∑ y : Spin n, if ε*n < |magnetization y| then
      doublePlantWeight β x y else 0) ≤
        Real.exp (-(q*ε^2*n/2))*(Real.sqrt (1-q))⁻¹ := by
  rw [Finset.sum_comm]
  simp_rw [doublePlantWeight_comm β]
  exact doublePlantWeight_magnetization_tail β q ε hq0 hq1 hε hn

noncomputable def pairSpinFrequency {n : ℕ} (x y : Spin n) (a b : Bool) : ℝ :=
  (∑ i : Fin n, if x i=a ∧ y i=b then (1:ℝ) else 0)/(n:ℝ)

lemma pairSpinFrequency_expansion {n : ℕ} (hn : 0 < n) (x y : Spin n) (a b : Bool) :
    pairSpinFrequency x y a b - 1/4 =
      ((if a then 1 else -1)*magnetization x +
        (if b then 1 else -1)*magnetization y +
        (if a then 1 else -1)*(if b then 1 else -1)*replicaOverlap x y)/(4*n) := by
  have hh (i : Fin n) : (if x i=a ∧ y i=b then (1:ℝ) else 0) =
      (1+(if a then 1 else -1)*spin x i+(if b then 1 else -1)*spin y i+
        (if a then 1 else -1)*(if b then 1 else -1)*spin x i*spin y i)/4 := by
    cases a <;> cases b <;> cases hx : x i <;> cases hy : y i <;> norm_num [spin, hx, hy]
  have hs : (∑ i : Fin n, if x i=a ∧ y i=b then (1:ℝ) else 0) =
      ((n:ℝ)+(if a then 1 else -1)*magnetization x +
       (if b then 1 else -1)*magnetization y +
       (if a then 1 else -1)*(if b then 1 else -1)*replicaOverlap x y)/4 := by
    simp_rw [hh]
    rw [← Finset.sum_div]
    congr 1
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum, mul_assoc,
      magnetization, replicaOverlap]
  rw [pairSpinFrequency, hs]
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp
  ring

lemma pairSpinFrequency_deviation {n : ℕ} (hn : 0 < n) (x y : Spin n) (a b : Bool) :
    |pairSpinFrequency x y a b-1/4| ≤
      (|magnetization x|+|magnetization y|+|replicaOverlap x y|)/(4*n) := by
  rw [pairSpinFrequency_expansion hn, abs_div, abs_of_pos (by positivity : (0:ℝ)<4*n)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh := (abs_add_le
    ((if a then 1 else -1)*magnetization x+(if b then 1 else -1)*magnetization y)
    ((if a then 1 else -1)*(if b then 1 else -1)*replicaOverlap x y)).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  cases a <;> cases b <;> simpa only [Bool.false_eq_true, ↓reduceIte, mul_one, one_mul, neg_mul,
    neg_neg, abs_neg] using hh

theorem doublePlantWeight_pair_frequency_tail (β q ε : ℝ)
    (hβq : β^2 < q) (hq1 : q < 1) (hε : 0 < ε) {n : ℕ} (hn : 0 < n) (a b : Bool) :
    (∑ x : Spin n, ∑ y : Spin n, if ε < |pairSpinFrequency x y a b-1/4| then
      doublePlantWeight β x y else 0) ≤
      3*Real.exp (-((q-β^2)*ε^2*n/2))*(Real.sqrt (1-q))⁻¹ := by
  let c := Real.exp (-((q-β^2)*ε^2*n/2))*(Real.sqrt (1-q))⁻¹
  have hq0 : 0 < q := (sq_nonneg β).trans_lt hβq
  have hpoint (x y : Spin n) :
      (if ε < |pairSpinFrequency x y a b-1/4| then doublePlantWeight β x y else 0) ≤
      (if ε*n < |magnetization x| then doublePlantWeight β x y else 0) +
      (if ε*n < |magnetization y| then doublePlantWeight β x y else 0) +
      (if ε*n < |replicaOverlap x y| then doublePlantWeight β x y else 0) := by
    have hp := (doublePlantWeight_pos β hn x y).le
    have hd := pairSpinFrequency_deviation hn x y a b
    have hN : (0:ℝ)<4*n := by positivity
    have he : ε < |pairSpinFrequency x y a b-1/4| →
        ε*n < |magnetization x| ∨ ε*n < |magnetization y| ∨ ε*n < |replicaOverlap x y| := by
      intro hh
      by_contra h
      push Not at h
      have hx := (le_div_iff₀ hN).mp hd
      nlinarith [h.1,h.2.1,h.2.2]
    split_ifs with h h1 h2 h3 <;> simp_all <;> linarith
  have hb : Real.exp (-(q*ε^2*n/2))*(Real.sqrt (1-q))⁻¹ ≤ c := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg β) (sq_nonneg ε)) (Nat.cast_nonneg (α := ℝ) n)]
  have hx := (doublePlantWeight_magnetization_tail β q ε hq0 hq1 hε hn).trans hb
  have hy := (doublePlantWeight_right_magnetization_tail β q ε hq0 hq1 hε hn).trans hb
  have hr := doublePlantWeight_overlap_tail β q ε hβq hq1 hε hn
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun y _ => hpoint x y))
  simp only [Finset.sum_add_distrib] at hs
  calc
    _ ≤ _ := hs
    _ ≤ c+c+c := add_le_add (add_le_add hx hy) hr
    _ = _ := by dsimp [c]; ring

end SKGapCutoff

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

end

end OAI
