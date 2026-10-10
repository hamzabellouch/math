import OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-!
# Weighted rows and the localized square estimate

Finite weighted Cauchy--Schwarz proves the localized Schur estimate in
`q:weighted-rows`. Constancy of the site factor on the support replaces a
level-set decomposition. Summing the localized estimates only uses a bound
at the support of the vector; no commutation with a projection is needed.
-/

namespace TwoPointCorrelations

open Finset

variable {ι δ : Type*} [Fintype ι] [Fintype δ]

lemma weighted_row_square (B : ι → ι → ℝ) (g a : ι → ℝ) (c : ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hg : ∀ i, 0 < g i)
    (hrow : ∀ i, ∑ j, B i j * g j / g i ≤ c * a i)
    (v : ι → ℝ) (i : ι) :
    (∑ j, B i j * v j) ^ 2 ≤
      (c * a i) * ∑ j, B i j * g i / g j * (v j) ^ 2 := by
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul univ
    (f := fun j => B i j * g j / g i)
    (g := fun j => B i j * g i / g j * (v j) ^ 2)
    (r := fun j => B i j * v j)
    (fun j _ => div_nonneg (mul_nonneg (hB i j) (hg j).le) (hg i).le)
    (fun j _ => mul_nonneg (div_nonneg (mul_nonneg (hB i j) (hg i).le) (hg j).le) (sq_nonneg _))
    (fun j _ => le_of_eq (by field_simp [(hg i).ne', (hg j).ne']))
  exact hcs.trans (mul_le_mul_of_nonneg_right (hrow i)
    (sum_nonneg (fun j _ => mul_nonneg
      (div_nonneg (mul_nonneg (hB i j) (hg i).le) (hg j).le) (sq_nonneg _))))

lemma weighted_column_bound (B : ι → ι → ℝ) (g a : ι → ℝ) (c : ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hsymm : ∀ i j, B i j = B j i)
    (hlevel : ∀ i j, B i j ≠ 0 → a i = a j)
    (hrow : ∀ i, ∑ j, B i j * g j / g i ≤ c * a i) (j : ι) :
    ∑ i, a i * B i j * g i / g j ≤ c * (a j) ^ 2 := by
  have heq : (∑ i, a i * B i j * g i / g j) =
      a j * ∑ i, B j i * g i / g j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    by_cases hij : B i j = 0
    · simp [hij, ← hsymm i j]
    · rw [hlevel i j hij, hsymm i j]
      ring
  rw [heq]
  calc
    _ ≤ a j * (c * a j) := mul_le_mul_of_nonneg_left (hrow j) (ha j)
    _ = _ := by ring

/-- The finite localized square bound. The input kernel is nonnegative,
so it can in particular be the entrywise norm of a Hermitian matrix. -/
theorem weighted_kernel_localized_square (B : ι → ι → ℝ)
    (g a : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hB : ∀ i j, 0 ≤ B i j) (hg : ∀ i, 0 < g i) (ha : ∀ i, 0 ≤ a i)
    (hsymm : ∀ i j, B i j = B j i)
    (hlevel : ∀ i j, B i j ≠ 0 → a i = a j)
    (hrow : ∀ i, ∑ j, B i j * g j / g i ≤ c * a i)
    (v : ι → ℝ) :
    ∑ i, (∑ j, B i j * v j) ^ 2 ≤ c ^ 2 * ∑ i, (a i) ^ 2 * (v i) ^ 2 := by
  calc
    _ ≤ ∑ i, (c * a i) * ∑ j, B i j * g i / g j * (v j) ^ 2 :=
      sum_le_sum (fun i _ => weighted_row_square B g a c hB hg hrow v i)
    _ = c * ∑ j, (∑ i, a i * B i j * g i / g j) * (v j) ^ 2 := by
      simp only [mul_sum, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ c * ∑ j, (c * (a j) ^ 2) * (v j) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (weighted_column_bound B g a c ha hsymm hlevel hrow j) (sq_nonneg _)
    _ = _ := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro j _
      ring

/-- The manuscript's localized square bound for a complex matrix. -/
theorem weighted_matrix_localized_square (A : ι → ι → ℂ)
    (g a : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hg : ∀ i, 0 < g i) (ha : ∀ i, 0 ≤ a i)
    (hsymm : ∀ i j, ‖A i j‖ = ‖A j i‖)
    (hlevel : ∀ i j, A i j ≠ 0 → a i = a j)
    (hrow : ∀ i, ∑ j, ‖A i j‖ * g j / g i ≤ c * a i)
    (v : ι → ℂ) :
    ∑ i, ‖∑ j, A i j * v j‖ ^ 2 ≤ c ^ 2 * ∑ i, (a i) ^ 2 * ‖v i‖ ^ 2 := by
  apply le_trans _ (weighted_kernel_localized_square (fun i j => ‖A i j‖) g a c hc
    (fun i j => norm_nonneg _) hg ha hsymm
    (fun i j hij => hlevel i j (fun hz => hij (by simp [hz]))) hrow (fun i => ‖v i‖))
  apply sum_le_sum
  intro i _
  apply (sq_le_sq₀ (norm_nonneg _)
    (sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr
  simpa only [norm_mul] using norm_sum_le univ (fun j => A i j * v j)

/-- Summing localized bounds only requires degree control where the
vector is nonzero. This is the support condition supplied by `v = E v`. -/
theorem localized_square_sum (A : δ → ι → ι → ℂ) (a : δ → ι → ℝ)
    (c M : ℝ) (v : ι → ℂ)
    (hlocal : ∀ d, ∑ i, ‖∑ j, A d i j * v j‖ ^ 2 ≤
      c ^ 2 * ∑ i, (a d i) ^ 2 * ‖v i‖ ^ 2)
    (hdegree : ∀ i, v i ≠ 0 → ∑ d, (a d i) ^ 2 ≤ M) :
    ∑ d, ∑ i, ‖∑ j, A d i j * v j‖ ^ 2 ≤ c ^ 2 * M * ∑ i, ‖v i‖ ^ 2 := by
  calc
    _ ≤ ∑ d, c ^ 2 * ∑ i, (a d i) ^ 2 * ‖v i‖ ^ 2 := sum_le_sum (fun d _ => hlocal d)
    _ = c ^ 2 * ∑ i, (∑ d, (a d i) ^ 2) * ‖v i‖ ^ 2 := by
      rw [← mul_sum, sum_comm]
      simp only [sum_mul]
    _ ≤ c ^ 2 * ∑ i, M * ‖v i‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply sum_le_sum
      intro i _
      by_cases hi : v i = 0
      · simp [hi]
      · exact mul_le_mul_of_nonneg_right (hdegree i hi) (sq_nonneg _)
    _ = _ := by rw [← mul_sum, mul_assoc]

/-- Entrywise application identity lets the matrix estimate feed directly
into the finite-dimensional Hilbert-space spectral transfer. -/
theorem weighted_operator_norm_le
    (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (A : ι → ι → ℂ) (hT : ∀ v i, T v i = ∑ j, A i j * v j)
    (g a : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hg : ∀ i, 0 < g i) (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hsymm : ∀ i j, ‖A i j‖ = ‖A j i‖)
    (hlevel : ∀ i j, A i j ≠ 0 → a i = a j)
    (hrow : ∀ i, ∑ j, ‖A i j‖ * g j / g i ≤ c * a i) : ‖T‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro v
  have hlocal := weighted_matrix_localized_square A g a c hc hg ha hsymm hlevel hrow
    (fun i => v i)
  have hsum : (∑ i, (a i) ^ 2 * ‖v i‖ ^ 2) ≤ ∑ i, ‖v i‖ ^ 2 := by
    apply sum_le_sum
    intro i _
    have hi : (a i) ^ 2 ≤ 1 := by nlinarith [ha i, ha1 i]
    exact (mul_le_mul_of_nonneg_right hi (sq_nonneg _)).trans_eq (one_mul _)
  have hs : ‖T v‖ ^ 2 ≤ c ^ 2 * ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simpa only [hT] using hlocal.trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg _))
  have hn : 0 ≤ c * ‖v‖ := mul_nonneg hc (norm_nonneg _)
  nlinarith [norm_nonneg (T v)]

end TwoPointCorrelations

end OAI
