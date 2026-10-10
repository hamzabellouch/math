import OAI.Geometry.TranslativeCovering.BlockCount

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace RowGrouping
open Finset
lemma binary_sum (q : ℝ) (J : ℕ) :
    ∑ k ∈ range J, (q+k+1)*(1/2:ℝ)^k =
      2*q+4-(2*q+2*J+4)*(1/2:ℝ)^J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, ih, pow_succ]
    push_cast
    ring

lemma binary_sum_le {q : ℝ} (hq : 0 ≤ q) (J : ℕ) :
    ∑ k ∈ range J, (q+k+1)*(1/2:ℝ)^k ≤ 2*q+4 := by
  rw [binary_sum]
  have hp : 0 ≤ (2*q+2*J+4)*(1/2:ℝ)^J := by positivity
  linarith

lemma weight_decompose {w : ℝ} (hw : w ≤ 1) (J : ℕ) :
    w ≤ (1/2:ℝ)^J + ∑ k ∈ range J, if (1/2:ℝ)^(k+1) < w then (1/2:ℝ)^k else 0 := by
  induction J with
  | zero => simpa using hw
  | succ J ih =>
    rw [sum_range_succ]
    by_cases h : (1/2:ℝ)^(J+1)<w
    · rw [ite_eq_left h]
      have hp : 0 ≤ (1/2:ℝ)^(J+1) := by positivity
      linarith
    · rw [ite_eq_right h]
      have hp : 0 ≤ ∑ k ∈ range J, if (1/2:ℝ)^(k+1)<w then (1/2:ℝ)^k else 0 := by
        apply sum_nonneg
        intro k _
        split_ifs <;> positivity
      linarith

lemma sum_bound {T : Type u_1} (S : Finset T) (w : T → ℝ)
    (hw : ∀ i ∈ S, w i ≤ 1) {C q : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q)
    (J : ℕ) (hcount : ∀ k < J,
      ((S.filter fun i => (1/2:ℝ)^(k+1)<w i).card : ℝ) ≤ C*(q+k+1)) :
    ∑ i ∈ S, w i ≤ S.card*(1/2:ℝ)^J+C*(2*q+4) := by
  classical
  calc
    _ ≤ ∑ i ∈ S, ((1/2:ℝ)^J+∑ k ∈ range J,
        if (1/2:ℝ)^(k+1)<w i then (1/2:ℝ)^k else 0) :=
      sum_le_sum fun i hi => weight_decompose (hw i hi) J
    _ = S.card*(1/2:ℝ)^J + ∑ k ∈ range J,
        ((S.filter fun i => (1/2:ℝ)^(k+1)<w i).card : ℝ)*(1/2:ℝ)^k := by
      rw [sum_add_distrib, sum_comm]
      simp only [sum_const, nsmul_eq_mul]
      congr 1
      apply sum_congr rfl
      intro k _
      rw [← sum_filter]
      simp
    _ ≤ S.card*(1/2:ℝ)^J + ∑ k ∈ range J, C*(q+k+1)*(1/2:ℝ)^k := by
      gcongr with k hk
      exact hcount k (mem_range.mp hk)
    _ = S.card*(1/2:ℝ)^J + C*(∑ k ∈ range J, (q+k+1)*(1/2:ℝ)^k) := by
      rw [mul_sum]
      congr 1
      apply sum_congr rfl
      intro _ _
      ring
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left (binary_sum_le hq J) hC) _

lemma log_row {T : Type u_2} (S : Finset T) (w : T → ℝ)
    (hn : ∀ i ∈ S, 0 ≤ w i) (hw : ∀ i ∈ S, w i ≤ 1)
    {C q q0 : ℝ} (hC : 0 ≤ C) (hq0 : 0 < q0) (hq : q0 ≤ q)
    (J : ℕ) (htail : (S.card:ℝ)*(1/2:ℝ)^J ≤ 1)
    (hcount : ∀ k < J,
      ((S.filter fun i => (1/2:ℝ)^(k+1)<w i).card : ℝ) ≤ C*(q+k+1)) :
    Real.log (1+∑ i ∈ S,w i) ≤ (2*C+(1+4*C)/q0)*q := by
  have hs := sum_bound S w hw hC (hq0.le.trans hq) J hcount
  have hn' : 0 ≤ ∑ i ∈ S,w i := sum_nonneg hn
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < 1+∑ i ∈ S,w i)
  have hmul : (1+4*C) ≤ ((1+4*C)/q0)*q := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hq0]
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  nlinarith

end RowGrouping

end OAI
