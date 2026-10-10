import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace OAI

/-!
# A lattice vector off all coordinate hyperplanes

For a matrix with nonzero determinant, use the integer coefficient vector
`(1,N,...,N^(n-1))`. Each coordinate of its row product is a nonzero
polynomial in `N`. Finitely many polynomials exclude only finitely many
integers, so a suitable integer `N` exists. This gives the vector selection
used to deduce ordinary ball bounds from vector-box counts.
-/

open Matrix Set
open scoped BigOperators

namespace DukePrimeDegree

/-- An invertible real matrix admits an integral row combination with no
zero coordinate. No bound on the chosen coefficients is required. -/
theorem exists_integer_row_all_ne_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    ∃ c : Fin n → ℤ, ∀ j, (Matrix.vecMul (fun i => (c i : ℝ)) A) j ≠ 0 := by
  classical
  let p : Fin n → Polynomial ℝ := fun j =>
    ∑ i : Fin n, Polynomial.monomial i.val (A i j)
  have hcoeff (i j : Fin n) : (p j).coeff i.val = A i j := by
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      exact ite_eq_right (fun h => hbi (Fin.ext h))
    · simp
  have hp (j : Fin n) : p j ≠ 0 := by
    intro hz
    apply hA
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i
    rw [← hcoeff i j, hz, Polynomial.coeff_zero]
  let bad : Fin n → Set ℤ := fun j => {N | (p j).eval (N : ℝ) = 0}
  have hbad (j : Fin n) : (bad j).Finite := by
    have hroots := Polynomial.finite_setOfPred_isRoot (hp j)
    have hinj : Function.Injective (fun N : ℤ => (N : ℝ)) := Int.cast_injective
    simpa only [bad, Set.preimage_ofPred_eq, Polynomial.IsRoot] using
      hroots.preimage hinj.injOn
  have hfinite : (⋃ j, bad j).Finite := Set.finite_iUnion hbad
  obtain ⟨N, _, hN⟩ := (Set.infinite_univ : (Set.univ : Set ℤ).Infinite).exists_notMem_finite hfinite
  refine ⟨fun i => N ^ i.val, fun j => ?_⟩
  have hNj : (p j).eval (N : ℝ) ≠ 0 := by
    intro hz
    exact hN (Set.mem_iUnion.mpr ⟨j, hz⟩)
  simpa [p, Matrix.vecMul, dotProduct, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, mul_comm] using hNj

/-- Every additive integer lattice containing the rows of an invertible
real matrix contains a vector with all coordinates nonzero. -/
theorem submodule_exists_all_coordinates_ne_zero {n : ℕ}
    (Λ : Submodule ℤ (Fin n → ℝ)) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) (hrows : ∀ i, A i ∈ Λ) :
    ∃ v ∈ Λ, ∀ j, v j ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_integer_row_all_ne_zero A hA
  refine ⟨Matrix.vecMul (fun i => (c i : ℝ)) A, ?_, hc⟩
  have hsum : (∑ i : Fin n, c i • A i) ∈ Λ :=
    Λ.sum_mem fun i _ => Λ.smul_mem (c i) (hrows i)
  convert hsum using 1
  ext j
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply, zsmul_eq_mul]

end DukePrimeDegree

end OAI
