import OAI.Probability.InvariantIsing.Fields.FieldParameterOrder

namespace OAI

/-! The finite-dimensional Hessian argument in `fld:concavity`: a
symmetric matrix with nonpositive off-diagonal entries and nonnegative
row sums is nonnegative as a quadratic form, also after positive scaling. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma field_quadratic_nonneg_of_row_sums {n : ℕ} (M : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, M i j = M j i)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (hrow : ∀ i, 0 ≤ ∑ j, M i j) (x : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, M i j * x i * x j := by
  let S := ∑ i, ∑ j, M i j * (x i - x j) ^ 2
  let R := ∑ i, ∑ j, M i j * (x i) ^ 2
  let Q := ∑ i, ∑ j, M i j * x i * x j
  have hS : S ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro j _
    by_cases hij : i = j
    · subst j
      simp
    · exact mul_nonpos_of_nonpos_of_nonneg (hoff i j hij) (sq_nonneg _)
  have hR : 0 ≤ R := by
    apply Finset.sum_nonneg
    intro i _
    rw [← Finset.sum_mul]
    exact mul_nonneg (hrow i) (sq_nonneg _)
  have hswap : (∑ i, ∑ j, M i j * (x j) ^ 2) = R := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have he : S = 2 * R - 2 * Q := by
    calc
      S = ∑ i, ∑ j, ((M i j * (x i) ^ 2 + M i j * (x j) ^ 2) -
          2 * (M i j * x i * x j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = R + (∑ i, ∑ j, M i j * (x j) ^ 2) - 2 * Q := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, R, Q]
      _ = 2 * R - 2 * Q := by rw [hswap]; ring
  dsimp only [Q] at he
  linarith

theorem field_quadratic_nonneg_of_positive_scaling {n : ℕ}
    (M : Fin n → Fin n → ℝ) (h : Fin n → ℝ)
    (hsym : ∀ i j, M i j = M j i)
    (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (hpos : ∀ i, 0 < h i) (hrow : ∀ i, 0 ≤ ∑ j, M i j * h j)
    (x : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, M i j * x i * x j := by
  let A := fun i j => h i * M i j * h j
  have hAsym : ∀ i j, A i j = A j i := by
    intro i j
    dsimp only [A]
    rw [hsym i j]
    ring
  have hAoff : ∀ i j, i ≠ j → A i j ≤ 0 := by
    intro i j hij
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (hpos i).le (hoff i j hij)) (hpos j).le
  have hArow : ∀ i, 0 ≤ ∑ j, A i j := by
    intro i
    have he : (∑ j, A i j) = h i * ∑ j, M i j * h j := by
      simp only [A, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    exact mul_nonneg (hpos i).le (hrow i)
  have hq := field_quadratic_nonneg_of_row_sums A hAsym hAoff hArow (fun i => x i / h i)
  convert hq using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [A]
  field_simp [(hpos i).ne', (hpos j).ne']

end InvariantIsing

end

end OAI
