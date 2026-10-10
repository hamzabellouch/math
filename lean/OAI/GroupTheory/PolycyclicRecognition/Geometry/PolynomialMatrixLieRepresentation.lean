import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialModelExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraHomLieDifferential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FaithfulDifferential

namespace OAI

/-! # Lie differentials of the polynomial-coordinate representation -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n m : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b))

def polynomialMatrixLieRepresentation : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ :=
  (unitsHomLieDifferential (polynomialMatrixRepresentation b B)
    (contDiff_polynomialMatrixRepresentation b B).contMDiff).comp P.tangentEquiv.toLieHom

theorem polynomialMatrixLieRepresentation_injective :
    Function.Injective (polynomialMatrixLieRepresentation b B) := by
  have hi := injective_algebra_differential
    PolynomialExponentialCoordinates.isGroupExponential_identity
    (polynomialMatrixRepresentation b B) (polynomialMatrixRepresentation_injective b B)
    (unitsHomLieDifferential (polynomialMatrixRepresentation b B)
      (contDiff_polynomialMatrixRepresentation b B).contMDiff).toLinearMap.toContinuousLinearMap
    (hasMFDerivAt_unitsHomLieDifferential (polynomialMatrixRepresentation b B)
      (contDiff_polynomialMatrixRepresentation b B).contMDiff)
  exact hi.comp P.tangentEquiv.injective

theorem polynomialMatrixLieRepresentation_exp (x : L) :
    polynomialMatrixRepresentation b B x =
      algebraExpUnit (polynomialMatrixLieRepresentation b B x) := by
  have h := hom_exp_eq_algebraExpUnit
    PolynomialExponentialCoordinates.isGroupExponential_identity
    (polynomialMatrixRepresentation b B)
    (unitsHomLieDifferential (polynomialMatrixRepresentation b B)
      (contDiff_polynomialMatrixRepresentation b B).contMDiff).toLinearMap.toContinuousLinearMap
    (hasMFDerivAt_unitsHomLieDifferential (polynomialMatrixRepresentation b B)
      (contDiff_polynomialMatrixRepresentation b B).contMDiff) (P.tangentEquiv x)
  change polynomialMatrixRepresentation b B (P.tangentEquiv x) =
    algebraExpUnit (polynomialMatrixLieRepresentation b B x) at h
  rwa [P.tangentEquiv_apply] at h

end PolycyclicRecognition

end

end OAI
