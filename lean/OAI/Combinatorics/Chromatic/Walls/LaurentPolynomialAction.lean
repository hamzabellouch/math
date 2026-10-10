import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.LaurentIdealCoefficients

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {R : Type*} [CommRing R] [Algebra ℚ R]

noncomputable def polynomialLinear : Polynomial R →ₗ[ℚ] LaurentSeries R where
  toFun := polynomial
  map_add' := polynomial.map_add
  map_smul' q p := by
    change polynomial (q • p)=q • polynomial p
    induction p using Polynomial.induction_on' with
    | add p r hp hr => simp only [smul_add,map_add,hp,hr]
    | monomial n r =>
      simp only [Polynomial.smul_monomial,polynomial_monomial]
      exact (single.linearMap (R:=ℚ) (-(n:ℤ))).map_smul q r

noncomputable def mulPolynomial (k : LaurentSeries R) : Polynomial R →ₗ[ℚ] LaurentSeries R :=
  (LinearMap.mulLeft ℚ k).comp polynomialLinear
@[simp] lemma mulPolynomial_apply (k : LaurentSeries R) (p : Polynomial R) :
    mulPolynomial k p=k*polynomial p := rfl
noncomputable def mulPolynomialCoeff (k : LaurentSeries R) (j : ℤ) : Polynomial R →ₗ[ℚ] R :=
  (coeff.linearMap (R:=ℚ) (-j)).comp (mulPolynomial k)
@[simp] lemma mulPolynomialCoeff_apply (k : LaurentSeries R) (j : ℤ) (p : Polynomial R) :
    mulPolynomialCoeff k j p=(k*polynomial p).coeff (-j) := rfl
lemma mulPolynomialCoeff_mem (J : Ideal R) (k : LaurentSeries R) (j : ℤ) (p : Polynomial R)
    (hp : ∀ n,p.coeff n∈J) : mulPolynomialCoeff k j p∈J := by
  rw [mulPolynomialCoeff_apply,mul_comm]
  exact coeff_mul_mem J _ _ (polynomial_coeff_mem J p hp) _
end ElementaryPositivity.LaurentAtInfinity

end

end OAI
