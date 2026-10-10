import OAI.Algebra.DepthFive.MixedOperator
import OAI.Algebra.DepthFive.IntegerRank

namespace OAI

noncomputable section

namespace Problem335

open MvPolynomial

variable {K L σ : Type*} [CommSemiring K] [CommSemiring L]

/-- Coefficient extension commutes with each differential or multiplication step. -/
theorem map_variableOperator (f : K →+* L) (isV : σ → Bool) (i : σ)
    (p : MvPolynomial σ K) :
    map f (variableOperator isV i p) = variableOperator isV i (map f p) := by
  cases hi : isV i <;> simp [variableOperator, hi, pderiv_map]

/-- The full mixed operator is natural under every homomorphism of coefficient
semirings. In particular its unnormalized integer matrix extends to any field. -/
theorem map_mixedOperator (f : K →+* L) (isV : σ → Bool)
    (p q : MvPolynomial σ K) :
    map f (mixedOperator isV p q) = mixedOperator isV (map f p) (map f q) := by
  induction p using MvPolynomial.induction_on generalizing q with
  | C a =>
      simp [smul_eq_C_mul]
  | add p r hp hr =>
      simp [hp, hr]
  | mul_X p i hp =>
      rw [mixedOperator_mul_apply, map_mul, mixedOperator_mul_apply,
        hp, map_X, mixedOperator_X, mixedOperator_X, map_variableOperator]

/-- The coefficient matrix in arbitrary selected source and target monomials.
When the selections enumerate bidegree fibers, this is the restricted operator
matrix in the unnormalized monomial bases. -/
def mixedMonomialMatrix {I J : Type*} (isV : σ → Bool)
    (p : MvPolynomial σ K) (source : I → σ →₀ ℕ) (target : J → σ →₀ ℕ) :
    Matrix J I K :=
  fun j i => (mixedOperator isV p (monomial (source i) 1)).coeff (target j)

theorem mixedMonomialMatrix_map {I J : Type*} (f : K →+* L)
    (isV : σ → Bool) (p : MvPolynomial σ K)
    (source : I → σ →₀ ℕ) (target : J → σ →₀ ℕ) :
    mixedMonomialMatrix isV (map f p) source target =
      (mixedMonomialMatrix isV p source target).map f := by
  ext j i
  have h := congrArg (fun polynomial => polynomial.coeff (target j))
    (map_mixedOperator f isV p (monomial (source i) 1))
  simpa [mixedMonomialMatrix, coeff_map] using h.symm

/-- Integral mixed operators have field-independent monomial-matrix rank in
characteristic zero, with no embedding between the two fields required. -/
theorem integer_mixedMonomialMatrix_rank_eq
    {I J : Type*} [Fintype I] [Fintype J]
    (K L : Type*) [Field K] [CharZero K] [Field L] [CharZero L]
    (isV : σ → Bool) (p : MvPolynomial σ ℤ)
    (source : I → σ →₀ ℕ) (target : J → σ →₀ ℕ) :
    (mixedMonomialMatrix isV (map (Int.castRingHom K) p) source target).rank =
      (mixedMonomialMatrix isV (map (Int.castRingHom L) p) source target).rank := by
  rw [mixedMonomialMatrix_map, mixedMonomialMatrix_map]
  exact integer_matrix_rank_eq K L _

end Problem335

end

end OAI
