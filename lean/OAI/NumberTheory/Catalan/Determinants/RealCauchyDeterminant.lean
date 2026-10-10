import OAI.NumberTheory.Catalan.Estimates.MixedOneStart
import OAI.NumberTheory.Catalan.Estimates.RealCauchyStep
import OAI.NumberTheory.Catalan.Estimates.RealPermutationAlgebra

namespace OAI

noncomputable section
open Set
open scoped BigOperators

namespace InternalCatalan

private theorem vandermonde_prod_succ {m : ℕ} (t : Fin (m + 1) → ℝ) :
    (∏ i : Fin (m + 1), ∏ j ∈ Finset.Ioi i, (t j - t i)) =
      (∏ j : Fin m, (t j.succ - t 0)) *
        (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (t j.succ - t i.succ)) := by
  simp only [Fin.prod_univ_succ, Fin.prod_Ioi_zero, Fin.prod_Ioi_succ]

private theorem cauchy_denominator_prod_succ {m : ℕ} (t s : Fin (m + 1) → ℝ) :
    (∏ i : Fin (m + 1), ∏ j : Fin (m + 1), (1 - t i * s j)) =
      (1 - t 0 * s 0) * (∏ i : Fin m, (1 - t i.succ * s 0)) *
        (∏ j : Fin m, (1 - t 0 * s j.succ)) *
          (∏ i : Fin m, ∏ j : Fin m, (1 - t i.succ * s j.succ)) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.prod_univ_succ, Finset.prod_mul_distrib]
  ring

theorem cauchy_det_eq_prod {m : ℕ} (t s : Fin m → ℝ)
    (h : ∀ i j, 1 - t i * s j ≠ 0) :
    Matrix.det (Matrix.of (fun i j : Fin m => (1 : ℝ) / (1 - t i * s j))) =
      ((∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (t j - t i)) *
        (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (s j - s i))) /
          (∏ i : Fin m, ∏ j : Fin m, (1 - t i * s j)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [cauchy_det_succ t s h,
      ih (fun i => t i.succ) (fun j => s j.succ) (fun i j => h i.succ j.succ)]
    simp only [vandermonde_prod_succ, cauchy_denominator_prod_succ,
      Finset.prod_div_distrib]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem realCauchy_denominator_pos {m : ℕ} (t s : Fin m → ℝ)
    (ht : ∀ i, t i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1)
    (i j : Fin m) : 0 < 1 - t i * s j :=
  mixed_affine_denominator_pos (ht i) ⟨(hs j).1.le, (hs j).2.le⟩

theorem realCauchy_det_eq_prod {m : ℕ} (t s : Fin m → ℝ)
    (ht : ∀ i, t i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    Matrix.det (Matrix.of (fun i j : Fin m => (1 : ℝ) / (1 - t i * s j))) =
      ((∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (t j - t i)) *
        (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (s j - s i))) /
          (∏ i : Fin m, ∏ j : Fin m, (1 - t i * s j)) :=
  cauchy_det_eq_prod t s (fun i j => (realCauchy_denominator_pos t s ht hs i j).ne')

theorem doubleRealIntegrand_eq_products (N : ℕ) (t s : Fin (n N) → ℝ)
    (ht : ∀ i, t i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) :
    doubleRealIntegrand N t s =
      Matrix.det (Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (t i))) *
        (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (t j - t i)) *
        (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)) ^ 2 *
        (∏ j : Fin (n N), (s j) ^ b N * (1 - s j) ^ q N) /
        (∏ i : Fin (n N), ∏ j : Fin (n N), (1 - t i * s j)) := by
  have hcolumn := filteredColumn_det_eq_prod N s
  change Matrix.det (Matrix.of (fun j k : Fin (n N) =>
    (filteredColumn N k.val).eval (s j))) = _ at hcolumn
  unfold doubleRealIntegrand
  rw [realCauchy_det_eq_prod t s ht hs, hcolumn]
  ring

end InternalCatalan

end

end OAI
