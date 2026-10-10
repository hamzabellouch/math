import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialExponentialCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialLieWordCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateOrbit

namespace OAI

/-! # A faithful finite-dimensional representation in polynomial coordinates -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ} (b : Module.Basis (Fin n) ℝ L)

def polynomialModelCoordinate (i : Fin n) (x : L) : ℝ := b.repr x i

def polynomialModelLetters : Fin 2 → Fin n → MvPolynomial (Fin n) (L → ℝ) :=
  ![(fun j => MvPolynomial.X j), (fun j => MvPolynomial.C (fun g => b.repr g j))]

def polynomialModelProduct (i : Fin n) : MvPolynomial (Fin n) (L → ℝ) :=
  dynkinCoordinatePolynomial b P.coefficients (polynomialModelLetters b) i

theorem polynomialModelProduct_eval (g x : L) (i : Fin n) :
    polynomialModelCoordinate b i (x * g) =
      coordinatePolynomialEvaluation (polynomialModelCoordinate b)
        (polynomialModelProduct b i) g x := by
  rw [polynomialModelCoordinate, P.mul_eq]
  symm
  change (dynkinCoordinatePolynomial b P.coefficients (polynomialModelLetters b) i).eval₂
      (Pi.evalAlgHom ℝ (fun _ : L => ℝ) g).toRingHom (fun j => b.repr x j) = _
  apply eval_dynkinCoordinatePolynomial
  intro k j
  fin_cases k <;> simp [polynomialModelLetters]

theorem finiteDimensional_polynomialModelOrbit :
    FiniteDimensional ℝ (coordinateOrbitSpan (polynomialModelCoordinate b)) :=
  finiteDimensional_coordinateOrbitSpan_of_polynomial (polynomialModelCoordinate b)
    (polynomialModelProduct b) (fun g i x => polynomialModelProduct_eval b g x i)

theorem polynomialModelRepresentation_injective :
    Function.Injective (coordinateOrbitRepresentation (polynomialModelCoordinate b)) := by
  apply coordinateOrbitRepresentation_injective
  intro x y h
  apply b.repr.injective
  ext i
  exact congrFun h i

end PolycyclicRecognition

end

end OAI
