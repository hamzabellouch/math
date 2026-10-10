import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectPolynomialMaps
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateAction

namespace OAI

/-! # Polynomiality and linear coordinate readout for the semidirect representation -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n m d : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

theorem semidirectMatrixRepresentation_polynomial
    (c : Module.Basis (Fin d) ℝ (L × ℝ)) :
    letI := derivationSemidirectGroup D hD
    letI := derivationSemidirectLieGroup D hD
    ∀ B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (semidirectCoordinate b),
    HasPolynomialMatrixEntries (fun x =>
      (coordinateMatrixRepresentation (semidirectCoordinate b) B (c.equivFun.symm x) :
        Matrix (Fin m) (Fin m) ℝ)) := by
  let := derivationSemidirectGroup D hD
  let := derivationSemidirectLieGroup D hD
  intro B i j
  apply polynomial_coordinateMatrix
  intro a z q
  have h := polynomialSemidirectCoordinates_mul b D hD _ _
    (polynomialSemidirectCoordinates_mul b D hD _ _
      (polynomialSemidirectCoordinates_const b a) (polynomialSemidirectCoordinates_basis b c))
    (polynomialSemidirectCoordinates_const b z)
  exact coordinatePolynomial_iff_components.mp h q

def semidirectMatrixReadout :
    letI := derivationSemidirectGroup D hD
    ((Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (semidirectCoordinate b)) →
      Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] (L × ℝ) := by
  let := derivationSemidirectGroup D hD
  intro B
  exact (semidirectCoordinateLinear b).leftInverse.comp
    (coordinateMatrixReadout (semidirectCoordinate b) B)

theorem semidirectMatrixReadout_apply (g : L × ℝ) :
    letI := derivationSemidirectGroup D hD
    letI := derivationSemidirectLieGroup D hD
    ∀ B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (semidirectCoordinate b),
      semidirectMatrixReadout b D hD B
        (coordinateMatrixRepresentation (semidirectCoordinate b) B g) = g := by
  let := derivationSemidirectGroup D hD
  let := derivationSemidirectLieGroup D hD
  intro B
  change (semidirectCoordinateLinear b).leftInverse
    (coordinateMatrixReadout (semidirectCoordinate b) B
      (coordinateMatrixRepresentation (semidirectCoordinate b) B g)) = g
  rw [coordinateMatrixReadout_apply]
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (semidirectCoordinate_injective b)) g

end PolycyclicRecognition

end

end OAI
