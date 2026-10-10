import OAI.NumberTheory.TwoPoint.Bounds.PrimePaddingDeletion

namespace OAI

/-! Finite second moments for the positive row majorant used to delete
rare sites. Independence is used only under the auxiliary product law. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace FiniteLaw

lemma average_add {α : Type*} [Fintype α] (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.average (fun x => f x + g x) = μ.average f + μ.average g := by
  simp only [average, mul_add, sum_add_distrib]

lemma independent_average_coordinate_mul {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (μ : ι → FiniteLaw α) (i j : ι) (hij : i ≠ j) (f g : α → ℝ) :
    (independent μ).average (fun x => f (x i) * g (x j)) =
      (μ i).average f * (μ j).average g := by
  let F : ι → α → ℝ := fun k a =>
    (if k = i then f a else 1) * (if k = j then g a else 1)
  have he (x : ι → α) : (∏ k, F k (x k)) = f (x i) * g (x j) := by
    simp only [F, prod_mul_distrib]
    simp
  have hm (k : ι) : (μ k).average (F k) =
      (if k = i then (μ i).average f else 1) *
        (if k = j then (μ j).average g else 1) := by
    by_cases hki : k = i
    · subst k
      simp [F, hij]
    · by_cases hkj : k = j
      · subst k
        simp [F, hki]
      · simp [F, hki, hkj]
  calc
    _ = (independent μ).average (fun x => ∏ k, F k (x k)) := by simp only [he]
    _ = ∏ k, (μ k).average (F k) := independent_average_product μ F
    _ = _ := by simp only [hm, prod_mul_distrib]; simp

end FiniteLaw

lemma booleanLaw_indicator_average (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (booleanLaw q hq0 hq1).average (fun b => if b then (1 : ℝ) else 0) = q := by
  simp [booleanLaw, FiniteLaw.average]

lemma independent_boolean_count_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      booleanCount = ∑ i, q i := by
  rw [show booleanCount = (fun a : ι → Bool => ∑ i, if a i then (1 : ℝ) else 0) from rfl,
    FiniteLaw.average_sum]
  apply sum_congr rfl
  intro i _
  rw [FiniteLaw.independent_average_coordinate
    (fun k => booleanLaw (q k) (hq0 k) (hq1 k)) i
    (fun b => if b then (1 : ℝ) else 0), booleanLaw_indicator_average]

lemma independent_boolean_count_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun a => (booleanCount a) ^ 2) ≤ (∑ i, q i) ^ 2 + ∑ i, q i := by
  let μ := FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))
  have hp (i j : ι) : μ.average (fun a =>
      (if a i then (1 : ℝ) else 0) * (if a j then 1 else 0)) ≤
        q i * q j + if i = j then q i else 0 := by
    by_cases hij : i = j
    · subst j
      have he (a : ι → Bool) :
          (if a i then (1 : ℝ) else 0) * (if a i then 1 else 0) =
            if a i then 1 else 0 := by cases a i <;> norm_num
      simp only [he, ite_true]
      rw [FiniteLaw.independent_average_coordinate
        (fun k => booleanLaw (q k) (hq0 k) (hq1 k)) i
        (fun b => if b then (1 : ℝ) else 0), booleanLaw_indicator_average]
      nlinarith [sq_nonneg (q i)]
    · simp only [hij, ite_false, add_zero]
      exact le_of_eq ((FiniteLaw.independent_average_coordinate_mul
        (fun i => booleanLaw (q i) (hq0 i) (hq1 i)) i j hij
        (fun b => if b then (1 : ℝ) else 0) (fun b => if b then (1 : ℝ) else 0)).trans
          (by rw [booleanLaw_indicator_average, booleanLaw_indicator_average]))
  have he (a : ι → Bool) : (booleanCount a) ^ 2 =
      ∑ i, ∑ j, (if a i then (1 : ℝ) else 0) * (if a j then 1 else 0) := by
    simp only [booleanCount, pow_two, sum_mul, mul_sum]
    rw [sum_comm]
  change μ.average (fun a => (booleanCount a) ^ 2) ≤ (∑ i, q i) ^ 2 + ∑ i, q i
  simp_rw [he, μ.average_sum]
  calc
    _ ≤ ∑ i, ∑ j, (q i * q j + if i = j then q i else 0) :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => hp i j))
    _ = _ := by
      simp only [sum_add_distrib, ← mul_sum, sum_ite_eq, mem_univ, ite_true, ← sum_mul]
      ring

lemma independent_boolean_shifted_count_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun a => (booleanCount a + ∑ i, q i) ^ 2) ≤
        4 * (∑ i, q i) ^ 2 + ∑ i, q i := by
  let μ := FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))
  let V := ∑ i, q i
  have he (a : ι → Bool) : (booleanCount a + V) ^ 2 =
      (booleanCount a) ^ 2 + booleanCount a * (2 * V) + V ^ 2 := by ring
  change μ.average (fun a => (booleanCount a + V) ^ 2) ≤ 4 * V ^ 2 + V
  simp_rw [he]
  rw [μ.average_add, μ.average_add, μ.average_mul_const, μ.average_const]
  have hm := independent_boolean_count_average q hq0 hq1
  have hs := independent_boolean_count_square q hq0 hq1
  change μ.average booleanCount = V at hm
  change μ.average (fun a => (booleanCount a) ^ 2) ≤ V ^ 2 + V at hs
  change μ.average (fun a => (booleanCount a) ^ 2) +
      μ.average booleanCount * (2 * V) + V ^ 2 ≤ 4 * V ^ 2 + V
  rw [hm]
  nlinarith

lemma padding_weight_square_average (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) :
    (paddingOriginalLaw Q hQ).average (fun a => (paddingTiltWeight Q a) ^ 2) =
      ∏ p : Q, (1 + 24 / (p.val : ℝ)) := by
  have he (a : Q → Bool) : (paddingTiltWeight Q a) ^ 2 =
      ∏ p : Q, if a p then (25 : ℝ) else 1 := by
    rw [paddingTiltWeight, ← prod_pow]
    apply prod_congr rfl
    intro p _
    cases a p <;> norm_num
  simp_rw [he]
  rw [paddingOriginalLaw, FiniteLaw.independent_average_product
    (fun p : Q => paddingOriginalPrimeLaw p (hQ p p.property))
    (fun _ b => if b then (25 : ℝ) else 1)]
  apply prod_congr rfl
  intro p _
  simp [paddingOriginalPrimeLaw, booleanLaw, FiniteLaw.average]
  ring

end TwoPointCorrelations

end OAI
