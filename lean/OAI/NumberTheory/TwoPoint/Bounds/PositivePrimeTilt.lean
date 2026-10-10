import OAI.NumberTheory.TwoPoint.Bounds.BernoulliTail
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

/-! Tilting the prime divisibility law by the positive majorant of one
tuple of centered prime factors.  Selected primes have parameter
`(1 + q)/2`; every other prime keeps its original parameter. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def positiveCenterWeight (q : ι → ℝ) (S : Finset ι)
    (a : ι → Bool) : ℝ :=
  ∏ i, if i ∈ S then (if a i then 1 else 0) + q i else 1

noncomputable def positiveCenterNormalizer (q : ι → ℝ) (S : Finset ι) : ℝ :=
  ∏ i, if i ∈ S then 2 * q i else 1

noncomputable def positiveCenterParameter (q : ι → ℝ) (S : Finset ι) (i : ι) : ℝ :=
  if i ∈ S then (1 + q i) / 2 else q i

omit [Fintype ι] in
lemma positiveCenterParameter_nonneg (q : ι → ℝ) (S : Finset ι)
    (hq : ∀ i, 0 ≤ q i) (i : ι) : 0 ≤ positiveCenterParameter q S i := by
  unfold positiveCenterParameter
  split_ifs
  · exact div_nonneg (add_nonneg zero_le_one (hq i)) (by norm_num)
  · exact hq i

omit [Fintype ι] in
lemma positiveCenterParameter_le_one (q : ι → ℝ) (S : Finset ι)
    (hq : ∀ i, q i ≤ 1) (i : ι) : positiveCenterParameter q S i ≤ 1 := by
  unfold positiveCenterParameter
  split_ifs
  · linarith [hq i]
  · exact hq i

noncomputable def positiveCenterLaw (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) : FiniteLaw (ι → Bool) :=
  FiniteLaw.independent (fun i => booleanLaw (positiveCenterParameter q S i)
    (positiveCenterParameter_nonneg q S hq0 i) (positiveCenterParameter_le_one q S hq1 i))

lemma positiveCenterWeight_eq (q : ι → ℝ) (S : Finset ι) (a : ι → Bool) :
    positiveCenterWeight q S a = ∏ i ∈ S, ((if a i then 1 else 0) + q i) := by
  simp only [positiveCenterWeight, ← prod_filter, filter_mem_eq_inter, univ_inter]

lemma positiveCenterNormalizer_eq (q : ι → ℝ) (S : Finset ι) :
    positiveCenterNormalizer q S = ∏ i ∈ S, 2 * q i := by
  simp only [positiveCenterNormalizer, ← prod_filter, filter_mem_eq_inter, univ_inter]

lemma positiveCenterNormalizer_nonneg (q : ι → ℝ) (S : Finset ι)
    (hq : ∀ i, 0 ≤ q i) : 0 ≤ positiveCenterNormalizer q S := by
  unfold positiveCenterNormalizer
  apply prod_nonneg
  intro i _
  split_ifs
  · exact mul_nonneg (by norm_num) (hq i)
  · exact zero_le_one

lemma positive_center_tilt_weight (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (a : ι → Bool) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).weight a *
        positiveCenterWeight q S a =
      (positiveCenterLaw q S hq0 hq1).weight a * positiveCenterNormalizer q S := by
  simp only [FiniteLaw.independent, positiveCenterLaw, positiveCenterWeight,
    positiveCenterNormalizer, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> cases a i <;>
    simp [positiveCenterParameter, hi, booleanLaw] <;> ring

lemma positive_center_tilt_average (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (F : (ι → Bool) → ℝ) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
        (fun a => positiveCenterWeight q S a * F a) =
      positiveCenterNormalizer q S * (positiveCenterLaw q S hq0 hq1).average F := by
  simp only [FiniteLaw.average, mul_sum]
  apply sum_congr rfl
  intro a _
  rw [← mul_assoc, positive_center_tilt_weight]
  ring

lemma positive_center_tilt_total (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
        (positiveCenterWeight q S) = positiveCenterNormalizer q S := by
  simpa only [mul_one, FiniteLaw.average_const] using
    positive_center_tilt_average q S hq0 hq1 (fun _ => 1)

lemma positiveCenterParameter_sum_le (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) :
    (∑ i, positiveCenterParameter q S i) ≤ (S.card : ℝ) + ∑ i, q i := by
  calc
    _ ≤ ∑ i, ((if i ∈ S then (1 : ℝ) else 0) + q i) := by
      apply sum_le_sum
      intro i _
      unfold positiveCenterParameter
      by_cases hi : i ∈ S
      · simp only [hi, ite_true]
        linarith [hq0 i]
      · simp only [hi, ite_false, zero_add, le_refl]
    _ = _ := by simp only [sum_add_distrib, sum_boole, filter_mem_eq_inter,
      univ_inter]

/-- The selected primes may be bounded simply by their number.  The
remaining Bernoulli mean is at most the original total reciprocal mass. -/
theorem positive_center_degree_tail (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (W : ℝ) (hW : 10 ≤ W) (hmass : (∑ i, q i) ≤ 2 * W * S.card) :
    (positiveCenterLaw q S hq0 hq1).probability
      (fun a => 6 * W * S.card < booleanCount a) ≤ Real.exp (-2 * W * S.card) := by
  have hJ : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hM : (∑ i, positiveCenterParameter q S i) ≤
      (S.card : ℝ) + 2 * W * S.card :=
    (positiveCenterParameter_sum_le q S hq0).trans (add_le_add le_rfl hmass)
  have hb := independent_boolean_tail (positiveCenterParameter q S)
    (positiveCenterParameter_nonneg q S hq0) (positiveCenterParameter_le_one q S hq1)
    1 ((S.card : ℝ) + 2 * W * S.card) (6 * W * S.card) (by norm_num) hM
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have he : Real.exp 1 - 1 ≤ (7 / 4 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have hW0 : 0 ≤ W := by linarith
  have hM0 : 0 ≤ (S.card : ℝ) + 2 * W * S.card :=
    add_nonneg hJ (mul_nonneg (mul_nonneg (by norm_num) hW0) hJ)
  have heM := mul_le_mul_of_nonneg_right he hM0
  nlinarith [mul_nonneg (sub_nonneg.mpr hW) hJ]

theorem positive_center_weighted_degree_tail (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (W : ℝ) (hW : 10 ≤ W) (hmass : (∑ i, q i) ≤ 2 * W * S.card) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun a => positiveCenterWeight q S a *
        if 6 * W * S.card < booleanCount a then 1 else 0) ≤
      positiveCenterNormalizer q S * Real.exp (-2 * W * S.card) := by
  rw [positive_center_tilt_average]
  exact mul_le_mul_of_nonneg_left (positive_center_degree_tail q S hq0 hq1 W hW hmass)
    (positiveCenterNormalizer_nonneg q S hq0)

end TwoPointCorrelations

end OAI
