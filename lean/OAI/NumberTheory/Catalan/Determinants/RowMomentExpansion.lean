import OAI.NumberTheory.Catalan.Polynomial.MixedPolynomial
import OAI.NumberTheory.Catalan.Polynomial.ZetaPolynomial

namespace OAI


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan

@[simp] theorem realPoly_coeff (F : ℤ[X]) (i : ℕ) :
    (realPoly F).coeff i = (F.coeff i : ℝ) := by
  rw [realPoly, Polynomial.coeff_map]
  rfl

theorem realPoly_support_subset_range (F : ℤ[X]) (D : ℕ)
    (hF : ∀ i, D ≤ i → F.coeff i = 0) :
    (realPoly F).support ⊆ Finset.range D := by
  intro i hi
  apply Finset.mem_range.mpr
  by_contra h
  have hzero : (realPoly F).coeff i = 0 := by
    rw [realPoly_coeff, hF i (by omega)]
    exact Int.cast_zero
  exact (Polynomial.mem_support_iff.mp hi) hzero

theorem mixedMoment_realPoly_X_pow_eq_sum_range (F : ℤ[X]) (D j : ℕ)
    (hF : ∀ i, D ≤ i → F.coeff i = 0) :
    mixedMoment (realPoly F) (X ^ j) =
      ∑ i ∈ Finset.range D,
        (F.coeff i : ℝ) * mixedMoment (X ^ i) (X ^ j) := by
  rw [mixedMoment_eq_sum]
  simp only [Polynomial.support_X_pow, Finset.sum_singleton,
    Polynomial.coeff_X_pow_self, mul_one]
  simpa only [Polynomial.sum_def, realPoly_coeff] using
    (Polynomial.sum_eq_of_subset (p := realPoly F)
      (fun i a => a * mixedMoment (X ^ i) (X ^ j))
      (fun _ => zero_mul _) (realPoly_support_subset_range F D hF))

theorem zetaMoment_realPoly_X_pow_eq_sum_range (F : ℤ[X]) (D j : ℕ)
    (hF : ∀ i, D ≤ i → F.coeff i = 0) :
    zetaMoment (realPoly F) (X ^ j) =
      ∑ i ∈ Finset.range D, (F.coeff i : ℝ) * zetaSeries i j := by
  rw [zetaMoment_eq_sum]
  simp only [Polynomial.support_X_pow, Finset.sum_singleton,
    Polynomial.coeff_X_pow_self, mul_one]
  simpa only [Polynomial.sum_def, realPoly_coeff] using
    (Polynomial.sum_eq_of_subset (p := realPoly F)
      (fun i a => a * zetaSeries i j)
      (fun _ => zero_mul _) (realPoly_support_subset_range F D hF))

theorem mixedMoment_rowP_X_pow_eq_sum_range {N : ℕ} (hN : 0 < N) (r j : ℕ) :
    mixedMoment (realPoly (rowP N r)) (X ^ j) =
      ∑ i ∈ Finset.range (H N),
        ((rowP N r).coeff i : ℝ) * mixedMoment (X ^ i) (X ^ j) := by
  exact mixedMoment_realPoly_X_pow_eq_sum_range (rowP N r) (H N) j
    (fun _ hi => rowP_coeff_eq_zero_of_ge hN hi)

theorem zetaMoment_rowD_X_pow_eq_sum_range {N : ℕ} (hN : 0 < N) (r j : ℕ) :
    zetaMoment (realPoly (rowD N r)) (X ^ j) =
      ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℝ) * zetaSeries i j := by
  exact zetaMoment_realPoly_X_pow_eq_sum_range (rowD N r) (H N) j
    (fun _ hi => rowD_coeff_eq_zero_of_ge hN hi)

end InternalCatalan

end

end OAI
