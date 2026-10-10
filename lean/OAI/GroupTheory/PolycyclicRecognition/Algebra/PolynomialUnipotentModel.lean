import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentPolynomialRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentMatrixProducts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticNilpotentExponential

namespace OAI

/-! # Unipotent realization of a polynomial exponential model

This construction is internal to the given polynomial model. It does not
assert the finite BCH formula for an arbitrary Lie group.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ} (b : Module.Basis (Fin n) ℝ L)

include b in
theorem exists_polynomial_unipotent_model :
    ∃ (m c : ℕ) (ρ : L →* Matrix.GeneralLinearGroup (Fin m) ℝ)
      (j : L →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ),
      Function.Injective ρ ∧ Function.Injective j ∧
      ContDiff ℝ ∞ (fun x => (ρ x : Matrix (Fin m) (Fin m) ℝ)) ∧
      (∀ x, ρ x = algebraExpUnit (j x)) ∧
      (∀ x, IsNilpotent ((ρ x : Matrix (Fin m) (Fin m) ℝ) - 1)) ∧
      (∀ l : List L, c ≤ l.length → (l.map j).prod = 0) := by
  let := finiteDimensional_polynomialModelOrbit b
  let m := Module.finrank ℝ (coordinateOrbitSpan (polynomialModelCoordinate b))
  let B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b) :=
    (Module.finBasis ℝ (coordinateOrbitSpan (polynomialModelCoordinate b))).equivFun.symm
  let j := polynomialMatrixLieRepresentation b B
  obtain ⟨c, hc⟩ := exists_vanishing_matrix_products_of_pointwise_nilpotent j
    (polynomialMatrixLieRepresentation_nilpotent b B)
  refine ⟨m, c, polynomialMatrixRepresentation b B, j,
    polynomialMatrixRepresentation_injective b B,
    polynomialMatrixLieRepresentation_injective b B,
    contDiff_polynomialMatrixRepresentation b B,
    polynomialMatrixLieRepresentation_exp b B, ?_, hc⟩
  intro x
  rw [polynomialMatrixLieRepresentation_exp, coe_algebraExpUnit]
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact isNilpotent_analytic_exp_sub_one (polynomialMatrixLieRepresentation_nilpotent b B x)

end PolycyclicRecognition

end

end OAI
