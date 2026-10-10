import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothPolynomialRepresentation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Analysis.Matrix.Normed

namespace OAI

/-! # Faithful smooth matrix representations of polynomial exponential models -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n m : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b))

def polynomialMatrixRepresentation : L →* Matrix.GeneralLinearGroup (Fin m) ℝ :=
  (Units.map LinearMap.toMatrixAlgEquiv'.toMonoidHom).comp
    (coordinateActionInBasis b B).asGroupHom

theorem polynomialMatrixRepresentation_apply (g : L) (i j : Fin m) :
    (polynomialMatrixRepresentation b B g : Matrix (Fin m) (Fin m) ℝ) i j =
      coordinateActionInBasis b B g (Pi.single j 1) i := rfl

theorem polynomialMatrixRepresentation_injective :
    Function.Injective (polynomialMatrixRepresentation b B) := by
  intro x y h
  apply coordinateActionInBasis_injective b B
  apply LinearMap.toMatrixAlgEquiv'.injective
  exact congrArg Units.val h

theorem contDiff_polynomialMatrixRepresentation :
    ContDiff ℝ ∞ (fun g =>
      (polynomialMatrixRepresentation b B g : Matrix (Fin m) (Fin m) ℝ)) := by
  let e : (Fin m → Fin m → ℝ) ≃ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ :=
    LinearEquiv.refl ℝ _
  have hf : ContDiff ℝ ∞ (fun g => fun i j =>
      coordinateActionInBasis b B g (Pi.single j 1) i) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_pi.mp (contDiff_coordinateActionInBasis b B (Pi.single j 1)) i
  exact e.toContinuousLinearEquiv.contDiff.comp hf

include b in
theorem exists_faithful_smooth_polynomialMatrixRepresentation :
    ∃ (m : ℕ) (ρ : L →* Matrix.GeneralLinearGroup (Fin m) ℝ),
      Function.Injective ρ ∧
      ContDiff ℝ ∞ (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) := by
  let := finiteDimensional_polynomialModelOrbit b
  let m := Module.finrank ℝ (coordinateOrbitSpan (polynomialModelCoordinate b))
  let B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b) :=
    (Module.finBasis ℝ (coordinateOrbitSpan (polynomialModelCoordinate b))).equivFun.symm
  exact ⟨m, polynomialMatrixRepresentation b B,
    polynomialMatrixRepresentation_injective b B, contDiff_polynomialMatrixRepresentation b B⟩

end PolycyclicRecognition

end

end OAI
