import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialUnipotentModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticNilpotentLogarithm

namespace OAI

/-! # Recovering Lie coordinates by a single finite matrix logarithm -/

noncomputable section
namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n m : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b))

theorem exists_uniform_polynomialMatrixLogarithm :
    ∃ d : ℕ, ∀ x : L,
      finiteNilpotentLog (d + 1)
        ((polynomialMatrixRepresentation b B x : Matrix (Fin m) (Fin m) ℝ) - 1) =
        polynomialMatrixLieRepresentation b B x := by
  obtain ⟨d, hd⟩ := exists_vanishing_matrix_products_of_pointwise_nilpotent
    (polynomialMatrixLieRepresentation b B) (polynomialMatrixLieRepresentation_nilpotent b B)
  refine ⟨d, fun x => ?_⟩
  have hx : polynomialMatrixLieRepresentation b B x ^ (d + 1) = 0 := by
    have h := hd (List.replicate (d + 1) x) (by simp)
    simpa only [List.map_replicate, List.prod_replicate] using h
  rw [polynomialMatrixLieRepresentation_exp, coe_algebraExpUnit]
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact finiteNilpotentLog_analytic_exp _ d hx

end PolycyclicRecognition

end

end OAI
