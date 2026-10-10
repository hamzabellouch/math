import OAI.NumberTheory.Catalan.Estimates.ExceptionalScalarBounds

namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial
open Classical
open scoped BigOperators

abbrev rawCoefficientIndex (N : ℕ) (t : Fin 3) :=
  Fin (if t = 0 then 1 else Cdegree N)

def rawCoefficientVector (N r j : ℕ) (t : Fin 3) (u : ℕ) : ℚ_[2] :=
  if t = 0 then smoothingColumn N r j
  else if t = 1 then ((Chebyshev.T ℤ (rowDistance N r : ℤ)).coeff u : ℚ_[2])
  else ((Int.sign (rowOffset N r) *
    (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).coeff u : ℤ) : ℚ_[2])

def rawCoefficientScalar (z : ℚ) (N j : ℕ) (t : Fin 3) (u : ℕ) : ℚ_[2] :=
  if t = 0 then 1
  else if t = 1 then exceptionScalar z N u j
  else boundaryScalar N u j

def rawCoefficientMinor (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k)) : ℚ_[2] :=
  Matrix.det (Matrix.of fun r k : Fin (n N) =>
    rawCoefficientVector N r.val (c k).val (τ k) (u k).val)

theorem rawColumnTerm_coefficient_expansion (z : ℚ) (N r j : ℕ) (t : Fin 3) :
    rawColumnTerm z N r j t =
      ∑ u : rawCoefficientIndex N t,
        rawCoefficientVector N r j t u.val * rawCoefficientScalar z N j t u.val := by
  by_cases h0 : t = 0
  · subst t
    simp [rawColumnTerm, rawCoefficientIndex, rawCoefficientVector, rawCoefficientScalar]
  · by_cases h1 : t = 1
    · subst t
      have hsum := Fin.sum_univ_eq_sum_range
        (fun u : ℕ => ((Chebyshev.T ℤ (rowDistance N r : ℤ)).coeff u : ℚ_[2]) *
          exceptionScalar z N u j) (Cdegree N)
      simpa [rawColumnTerm, rawCoefficientIndex, rawCoefficientVector,
        rawCoefficientScalar] using
        (exceptionColumn_eq_sum_exceptionScalar z N r j).trans hsum.symm
    · have h2 : t = 2 := by omega
      subst t
      have hsum := Fin.sum_univ_eq_sum_range
        (fun u : ℕ => ((Int.sign (rowOffset N r) *
          (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).coeff u : ℤ) : ℚ_[2]) *
            boundaryScalar N u j) (Cdegree N)
      simpa [rawColumnTerm, rawCoefficientIndex, rawCoefficientVector,
        rawCoefficientScalar] using
        (boundaryColumn_eq_sum_boundaryScalar N r j).trans hsum.symm

theorem rawColumnMinor_coefficient_expansion (z : ℚ) (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3) :
    Matrix.det (Matrix.of fun r k : Fin (n N) =>
      rawColumnTerm z N r.val (c k).val (τ k)) =
      ∑ u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k),
        (∏ k : Fin (n N), rawCoefficientScalar z N (c k).val (τ k) (u k).val) *
          rawCoefficientMinor N c τ u := by
  classical
  have hmatrix :
      (Matrix.of fun r k : Fin (n N) => rawColumnTerm z N r.val (c k).val (τ k)) =
        (Matrix.of fun r k : Fin (n N) =>
          ∑ a : rawCoefficientIndex N (τ k),
            rawCoefficientVector N r.val (c k).val (τ k) a.val *
              rawCoefficientScalar z N (c k).val (τ k) a.val) := by
    ext r k
    simp only [Matrix.of_apply, rawColumnTerm_coefficient_expansion]
  rw [hmatrix]
  calc
    _ = ∑ u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k),
        ∑ σ : Equiv.Perm (Fin (n N)), ((Equiv.Perm.sign σ : ℤ) : ℚ_[2]) *
          ∏ k : Fin (n N),
            rawCoefficientVector N (σ k).val (c k).val (τ k) (u k).val *
              rawCoefficientScalar z N (c k).val (τ k) (u k).val := by
      simp only [Matrix.det_apply', Matrix.of_apply, Fintype.prod_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [rawCoefficientMinor, Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Finset.prod_mul_distrib]
      ring

theorem rawCoefficientMinor_eq_zero_of_repeat_exception (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k))
    {i j : Fin (n N)} (hne : i ≠ j) (hi : τ i = 1) (hj : τ j = 1)
    (hu : (u i).val = (u j).val) : rawCoefficientMinor N c τ u = 0 := by
  unfold rawCoefficientMinor
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp [Matrix.of_apply, rawCoefficientVector, hi, hj, hu]

theorem rawCoefficientMinor_eq_zero_of_repeat_boundary (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k))
    {i j : Fin (n N)} (hne : i ≠ j) (hi : τ i = 2) (hj : τ j = 2)
    (hu : (u i).val = (u j).val) : rawCoefficientMinor N c τ u = 0 := by
  unfold rawCoefficientMinor
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp [Matrix.of_apply, rawCoefficientVector, hi, hj, hu]

theorem rawCoefficientMinor_exception_injOn (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k))
    (hdet : rawCoefficientMinor N c τ u ≠ 0) :
    Set.InjOn (fun k => (u k).val) {k | τ k = 1} := by
  intro i hi j hj hu
  by_contra hne
  exact hdet (rawCoefficientMinor_eq_zero_of_repeat_exception N c τ u hne hi hj hu)

theorem rawCoefficientMinor_boundary_injOn (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3)
    (u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k))
    (hdet : rawCoefficientMinor N c τ u ≠ 0) :
    Set.InjOn (fun k => (u k).val) {k | τ k = 2} := by
  intro i hi j hj hu
  by_contra hne
  exact hdet (rawCoefficientMinor_eq_zero_of_repeat_boundary N c τ u hne hi hj hu)

theorem rawColumnMinor_coefficient_expansion_injective (z : ℚ) (N : ℕ)
    (c : Fin (n N) → ↥(Finset.Ico (b N) (L N)))
    (τ : Fin (n N) → Fin 3) :
    Matrix.det (Matrix.of fun r k : Fin (n N) =>
      rawColumnTerm z N r.val (c k).val (τ k)) =
      ∑ u : ∀ k : Fin (n N), rawCoefficientIndex N (τ k) with
          Set.InjOn (fun k => (u k).val) {k | τ k = 1} ∧
          Set.InjOn (fun k => (u k).val) {k | τ k = 2},
        (∏ k : Fin (n N), rawCoefficientScalar z N (c k).val (τ k) (u k).val) *
          rawCoefficientMinor N c τ u := by
  classical
  rw [rawColumnMinor_coefficient_expansion]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro u hu hout
  have hnot : ¬(Set.InjOn (fun k => (u k).val) {k | τ k = 1} ∧
      Set.InjOn (fun k => (u k).val) {k | τ k = 2}) := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hout
  have hzero : rawCoefficientMinor N c τ u = 0 := by
    by_contra hne
    exact hnot ⟨rawCoefficientMinor_exception_injOn N c τ u hne,
      rawCoefficientMinor_boundary_injOn N c τ u hne⟩
  rw [hzero, mul_zero]

end InternalCatalan

end

end OAI
