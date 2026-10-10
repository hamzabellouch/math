import Mathlib.Algebra.Order.Field.GeomSum
import OAI.NumberTheory.Ostmann.Preliminaries.FiniteCauchyEstimate

namespace OAI

/-! # Rectangular polynomial truncation with a geometric error -/

namespace Ostmann
open scoped Classical BigOperators

theorem finite_geometric_tail_le (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (N K : ℕ) :
    (∑ i ∈ Finset.range N, if K < i then q ^ i else 0) ≤ q ^ (K + 1) / (1 - q) := by
  rw [← Finset.sum_filter]
  have he : {i ∈ Finset.range N | K < i} = Finset.Ico (K + 1) N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [he]
  exact geom_sum_Ico_le_of_lt_one hq hq1

theorem finite_geometric_sum_le (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (∑ i ∈ Finset.range N, q ^ i) ≤ 1 / (1 - q) := by
  simpa only [Nat.Ico_zero_eq_range, pow_zero] using
    (geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hq hq1)

noncomputable def rectangularPolynomialSum {E : Type*} [AddCommMonoid E]
    (c : ℕ → ℕ → E) (N K : ℕ) : E :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    if i ≤ K ∧ j ≤ K then c i j else 0

theorem rectangularPolynomialSum_error {E : Type*} [NormedAddCommGroup E]
    (c : ℕ → ℕ → E) (N K : ℕ) (M q : ℝ) (hM : 0 ≤ M)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hc : ∀ i < N, ∀ j < N, ‖c i j‖ ≤ M * q ^ i * q ^ j) :
    ‖(∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i j) -
      rectangularPolynomialSum c N K‖ ≤
        2 * M * q ^ (K + 1) / (1 - q) ^ 2 := by
  have he : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i j) -
      rectangularPolynomialSum c N K =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        if i ≤ K ∧ j ≤ K then 0 else c i j := by
    unfold rectangularPolynomialSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [he]
  let Q := ∑ i ∈ Finset.range N, q ^ i
  let T := ∑ i ∈ Finset.range N, if K < i then q ^ i else 0
  have hQ : Q ≤ 1 / (1 - q) := finite_geometric_sum_le q hq hq1 N
  have hT : T ≤ q ^ (K + 1) / (1 - q) := finite_geometric_tail_le q hq hq1 N K
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => pow_nonneg hq i)
  calc
    _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ‖if i ≤ K ∧ j ≤ K then (0 : E) else c i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (M * (if K < i then q ^ i else 0) * q ^ j +
          M * q ^ i * (if K < j then q ^ j else 0)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hh := hc i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
      by_cases hiK : i ≤ K <;> by_cases hjK : j ≤ K
      · simp [hiK, hjK, Nat.not_lt.mpr hiK, Nat.not_lt.mpr hjK]
      · simpa [hiK, hjK, Nat.not_lt.mpr hiK, Nat.lt_of_not_ge hjK] using hh
      · simpa [hiK, hjK, Nat.lt_of_not_ge hiK, Nat.not_lt.mpr hjK] using hh
      · simp only [hiK, hjK, false_and, ite_false, Nat.lt_of_not_ge hiK,
          Nat.lt_of_not_ge hjK, ite_true]
        exact hh.trans (le_add_of_nonneg_right (by positivity))
    _ = 2 * M * T * Q := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, Q, T]
      ring
    _ ≤ 2 * M * (q ^ (K + 1) / (1 - q)) * (1 / (1 - q)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hT (by positivity)) hQ hQ0 (by positivity)
    _ = _ := by field_simp

end Ostmann

end OAI
