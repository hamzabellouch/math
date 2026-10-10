import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianNormalHigherExteriorFiniteness
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.MvPolynomial.CommRing

namespace OAI

/-! # Polynomial coordinates on the exterior power of a free polynomial orbit

Evaluation at independent variables followed by the determinant sends a
polynomial wedge to its alternant. Multiplication by a shifted variable in
every coordinate becomes multiplication by the corresponding product.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Polynomial
variable (K : Type) [Field K]

def polynomialEvaluationVector (n : ℕ) :
    K[X] →ₗ[K] (Fin n → MvPolynomial (Fin n) K) :=
  LinearMap.pi (fun i => (Polynomial.aeval (MvPolynomial.X i)).toLinearMap)

def scalarDeterminantAlternating (n : ℕ) :
    (Fin n → MvPolynomial (Fin n) K) [⋀^Fin n]→ₗ[K] MvPolynomial (Fin n) K where
  toMultilinearMap :=
    (Matrix.detRowAlternating : (Fin n → MvPolynomial (Fin n) K)
      [⋀^Fin n]→ₗ[MvPolynomial (Fin n) K] MvPolynomial (Fin n) K).toMultilinearMap.restrictScalars K
  map_eq_zero_of_eq' _ _ _ h hij := Matrix.detRowAlternating.map_eq_zero_of_eq _ h hij

def polynomialDeterminantAlternating (n : ℕ) :
    K[X] [⋀^Fin n]→ₗ[K] MvPolynomial (Fin n) K :=
  (scalarDeterminantAlternating K n).compLinearMap (polynomialEvaluationVector K n)

def polynomialExteriorDeterminant (n : ℕ) :
    (⋀[K]^n K[X]) →ₗ[K] MvPolynomial (Fin n) K :=
  exteriorPower.alternatingMapLinearEquiv (polynomialDeterminantAlternating K n)

@[simp] theorem polynomialExteriorDeterminant_value (n : ℕ) (v : Fin n → K[X]) :
    polynomialExteriorDeterminant K n (exteriorPower.ιMulti K n v) =
      Matrix.det (fun i j => Polynomial.aeval (MvPolynomial.X j) (v i)) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem polynomialExteriorDeterminant_mul (n : ℕ) (p : K[X]) (w : ⋀[K]^n K[X]) :
    polynomialExteriorDeterminant K n
        (exteriorPower.map n (LinearMap.mulLeft K p) w) =
      (∏ i : Fin n, Polynomial.aeval (MvPolynomial.X i) p) *
        polynomialExteriorDeterminant K n w := by
  have he : (polynomialExteriorDeterminant K n).comp
      (exteriorPower.map n (LinearMap.mulLeft K p)) =
    (LinearMap.mulLeft K (∏ i : Fin n, Polynomial.aeval (MvPolynomial.X i) p)).comp
      (polynomialExteriorDeterminant K n) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, polynomialExteriorDeterminant_value,
      Function.comp_apply, LinearMap.mulLeft_apply, map_mul]
    exact Matrix.det_mul_row _ _
  exact LinearMap.congr_fun he w

theorem polynomialExteriorDeterminant_shift (n : ℕ) (c : K) (w : ⋀[K]^n K[X]) :
    polynomialExteriorDeterminant K n
        (exteriorPower.map n (LinearMap.mulLeft K (Polynomial.X - Polynomial.C c)) w) =
      (∏ i : Fin n, (MvPolynomial.X i - MvPolynomial.C c)) *
        polynomialExteriorDeterminant K n w := by
  have he (i : Fin n) : Polynomial.aeval (MvPolynomial.X i)
      (Polynomial.X - Polynomial.C c) = MvPolynomial.X i - MvPolynomial.C c := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    rfl
  refine (polynomialExteriorDeterminant_mul K n (Polynomial.X - Polynomial.C c) w).trans ?_
  exact congrArg (fun p => p * polynomialExteriorDeterminant K n w)
    (Finset.prod_congr rfl (fun i _ => he i))

theorem polynomialExteriorDeterminant_monomials (n : ℕ) :
    polynomialExteriorDeterminant K n
        (exteriorPower.ιMulti K n (fun i : Fin n => (Polynomial.X : K[X]) ^ i.val)) =
      Matrix.det (Matrix.vandermonde (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) K))) := by
  rw [polynomialExteriorDeterminant_value]
  have he : (fun i j : Fin n =>
      Polynomial.aeval (MvPolynomial.X j : MvPolynomial (Fin n) K) ((Polynomial.X : K[X]) ^ i.val)) =
      Matrix.transpose (Matrix.vandermonde (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) K))) := by
    funext i j
    simp only [map_pow, Polynomial.aeval_X, Matrix.transpose_apply, Matrix.vandermonde_apply]
  rw [he, Matrix.det_transpose]

theorem polynomialExteriorDeterminant_monomials_ne_zero (n : ℕ) :
    polynomialExteriorDeterminant K n
      (exteriorPower.ιMulti K n (fun i : Fin n => (Polynomial.X : K[X]) ^ i.val)) ≠ 0 := by
  rw [polynomialExteriorDeterminant_monomials]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr MvPolynomial.X_injective

end PolycyclicRecognition

end

end OAI
