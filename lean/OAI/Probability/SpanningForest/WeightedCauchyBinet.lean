import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Matrix
open Equiv Finset Function

namespace Problem336
namespace WeightedCauchyBinet

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
variable {R : Type*} [CommRing R]

theorem det_mul_expansion (A : Matrix n m R) (B : Matrix m n R) :
    (A * B).det = ∑ f : n → m, (A.submatrix id f).det * ∏ i, B (f i) i := by
  calc
    (A * B).det = ∑ f : n → m, ∑ σ : Equiv.Perm n,
        ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, A (σ i) (f i) * B (f i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum,
        Fintype.piFinset_univ]
      exact Finset.sum_comm
    _ = ∑ f : n → m, (A.submatrix id f).det * ∏ i, B (f i) i := by
      apply Finset.sum_congr rfl
      intro f _
      simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq,
        Finset.sum_mul, Finset.prod_mul_distrib, mul_assoc]

theorem ordered_cauchy_binet (A : Matrix n m R) (B : Matrix m n R) :
    (Fintype.card (Equiv.Perm n) : R) * (A * B).det =
      ∑ f : n → m, (A.submatrix id f).det * (B.submatrix f id).det := by
  have hperm (σ : Equiv.Perm n) :
      (∑ f : n → m, (A.submatrix id f).det *
        (((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, B (f (σ i)) i)) =
      (A * B).det := by
    rw [det_mul_expansion]
    apply Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl m))
    intro f
    have hdet := Matrix.det_permute' σ (A.submatrix id f)
    change (A.submatrix id f).det *
      (((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, B (f (σ i)) i) =
      (A.submatrix id (fun i => f (σ i))).det * ∏ i, B (f (σ i)) i
    have hmat : (A.submatrix id (fun i => f (σ i))) =
        (A.submatrix id f).submatrix id σ := rfl
    rw [hmat, hdet]
    ring
  symm
  calc
    (∑ f : n → m, (A.submatrix id f).det * (B.submatrix f id).det) =
        ∑ σ : Equiv.Perm n, ∑ f : n → m, (A.submatrix id f).det *
          (((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, B (f (σ i)) i) := by
      simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ _σ : Equiv.Perm n, (A * B).det := by
      apply Finset.sum_congr rfl
      intro σ _
      exact hperm σ
    _ = (Fintype.card (Equiv.Perm n) : R) * (A * B).det := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem weighted_gram_det [DecidableEq m] (A : Matrix n m R) (c : m → R) :
    (Fintype.card (Equiv.Perm n) : R) *
        (A * Matrix.diagonal c * A.transpose).det =
      ∑ f : n → m, (A.submatrix id f).det ^ 2 * ∏ i, c (f i) := by
  have hminor (f : n → m) :
      ((Matrix.diagonal c * A.transpose).submatrix f id).det =
        (∏ i, c (f i)) * (A.submatrix id f).det := by
    have hmatrix : (Matrix.diagonal c * A.transpose).submatrix f id =
        Matrix.of (fun i j => c (f i) * (A.submatrix id f).transpose i j) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.diagonal_mul, Matrix.transpose_apply,
        Matrix.of_apply, id_eq]
    rw [hmatrix, Matrix.det_mul_column, Matrix.det_transpose]
  rw [Matrix.mul_assoc, ordered_cauchy_binet]
  apply Finset.sum_congr rfl
  intro f _
  rw [hminor]
  ring

theorem weighted_gram_det_real [DecidableEq m] (A : Matrix n m ℝ) (c : m → ℝ) :
    (A * Matrix.diagonal c * A.transpose).det =
      (∑ f : n → m, (A.submatrix id f).det ^ 2 * ∏ i, c (f i)) /
        (Fintype.card n).factorial := by
  have h := weighted_gram_det A c
  rw [Fintype.card_perm] at h
  have hfac : ((Fintype.card n).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Fintype.card n)
  apply (eq_div_iff hfac).mpr
  simpa only [mul_comm] using h

omit [Fintype m] in

theorem det_submatrix_eq_zero_of_not_injective (A : Matrix n m R) {f : n → m}
    (hf : ¬ Function.Injective f) : (A.submatrix id f).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
  exact Matrix.det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix_apply, hij])

theorem weighted_gram_det_injective [DecidableEq m]
    (A : Matrix n m R) (c : m → R) :
    (Fintype.card (Equiv.Perm n) : R) *
        (A * Matrix.diagonal c * A.transpose).det =
      ∑ f : n → m with Function.Injective f,
        (A.submatrix id f).det ^ 2 * ∏ i, c (f i) := by
  classical
  rw [weighted_gram_det]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro f _ hf
  have hnot : ¬ Function.Injective f := by simpa only [Finset.mem_filter_univ] using hf
  rw [det_submatrix_eq_zero_of_not_injective A hnot]
  simp

theorem weighted_gram_det_nonneg [DecidableEq m]
    (A : Matrix n m ℝ) (c : m → ℝ) (hc : ∀ j, 0 ≤ c j) :
    0 ≤ (A * Matrix.diagonal c * A.transpose).det := by
  rw [weighted_gram_det_real]
  apply div_nonneg
  · exact Finset.sum_nonneg fun f _ =>
      mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun i _ => hc (f i))
  · positivity

theorem weighted_gram_det_pos [DecidableEq m]
    (A : Matrix n m ℝ) (c : m → ℝ) (hc : ∀ j, 0 < c j)
    (hA : ∃ f : n → m, (A.submatrix id f).det ≠ 0) :
    0 < (A * Matrix.diagonal c * A.transpose).det := by
  rw [weighted_gram_det_real]
  apply div_pos
  · apply Finset.sum_pos'
    · intro f _
      exact mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun i _ => (hc (f i)).le)
    · obtain ⟨f, hf⟩ := hA
      exact ⟨f, Finset.mem_univ _,
        mul_pos (sq_pos_of_ne_zero hf) (Finset.prod_pos fun i _ => hc (f i))⟩
  · exact_mod_cast Nat.factorial_pos (Fintype.card n)

end WeightedCauchyBinet
end Problem336

end

end OAI
