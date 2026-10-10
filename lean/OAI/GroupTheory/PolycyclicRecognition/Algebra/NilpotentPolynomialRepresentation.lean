import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialRepresentationCurves
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialOneParameterNilpotent

namespace OAI

/-! # Nilpotence of the faithful polynomial representation

The representation is polynomial on every straight one-parameter subgroup.
The actual Lie differential therefore consists of nilpotent matrices.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n m : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b))

theorem polynomialMatrixLieRepresentation_nilpotent (v : L) :
    IsNilpotent (polynomialMatrixLieRepresentation b B v) := by
  let A := polynomialMatrixLieRepresentation b B v
  let f : ℝ → Matrix (Fin m) (Fin m) ℝ :=
    fun t => (polynomialMatrixRepresentation b B (t • v) : Matrix (Fin m) (Fin m) ℝ)
  have hf0 : f 0 = 1 := by
    dsimp only [f]
    rw [zero_smul, ← P.one_eq_zero, map_one]
    rfl
  have hadd (s t : ℝ) : f (s + t) = f s * f t := by
    dsimp only [f]
    rw [← PolynomialExponentialCoordinates.smul_mul (L := L) v s t, map_mul]
    rfl
  have heq : f = fun t => NormedSpace.exp (t • A) := by
    funext t
    have h := congrArg Units.val (polynomialMatrixLieRepresentation_exp b B (t • v))
    simp only [coe_algebraExpUnit, map_smul] at h
    exact h
  have hzero : HasDerivAt f A 0 := by
    rw [heq]
    let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
    have h := hasDerivAt_exp_smul_const A (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  exact isNilpotent_of_polynomial_oneParameter hf0 hadd hzero
    (polynomial_matrixRepresentation_entry b B v)

include b in
theorem exists_faithful_nilpotent_matrixLieRepresentation :
    ∃ (m : ℕ) (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ),
      Function.Injective j ∧ ∀ x, IsNilpotent (j x) := by
  let := finiteDimensional_polynomialModelOrbit b
  let m := Module.finrank ℝ (coordinateOrbitSpan (polynomialModelCoordinate b))
  let B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b) :=
    (Module.finBasis ℝ (coordinateOrbitSpan (polynomialModelCoordinate b))).equivFun.symm
  exact ⟨m, polynomialMatrixLieRepresentation b B,
    polynomialMatrixLieRepresentation_injective b B,
    polynomialMatrixLieRepresentation_nilpotent b B⟩

end PolycyclicRecognition

end

end OAI
