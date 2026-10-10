import OAI.GroupTheory.PolycyclicRecognition.Geometry.AdjointMatrixHeight

namespace OAI

/-! # Determinant of the actual adjoint action on a triangular Lie model -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator
open Module LieAlgebra

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

theorem det_conjugationDifferential_exp {n : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ) (hρExp : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    LinearMap.det (conjugationDifferentialHom (E := E) (Exp x)).toLinearMap =
      Real.exp (LinearMap.trace ℝ _ (ad ℝ _ x)) := by
  rw [← LinearMap.det_toMatrix T.basis]
  change Matrix.det (adjointMatrixHom T.basis (Exp x)) = _
  rw [adjointMatrixHom_exp T.basis hExp j ρ hρ hρExp]
  rw [Matrix.det_of_isUpperTriangular (matrix_exp_upperTriangular _ (T.upper x))]
  simp_rw [matrix_exp_diagonal _ (T.upper x)]
  rw [← Real.exp_sum, LinearMap.trace_eq_matrix_trace ℝ T.basis]
  rfl

end PolycyclicRecognition

end

end OAI
