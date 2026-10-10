import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicAdjointExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularExponentialKernel

namespace OAI

/-! # Periods of the real triangular exponential are central

This reduces possible failure of injectivity to the central directions,
without a global exponential chart or a faithful group representation.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem lie_bracket_zero_of_exponential_eq_one
    {n : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {x : GroupLieAlgebra (𝓘(ℝ, E)) G} (hx : Exp x = 1)
    (y : GroupLieAlgebra (𝓘(ℝ, E)) G) : ⁅x, y⁆ = 0 := by
  let D := groupAdjointOperator (E := E) x
  let M := LinearMap.toMatrix T.basis T.basis (LieAlgebra.ad ℝ _ x)
  let f : (E →L[ℝ] E) →+* Matrix (Fin n) (Fin n) ℝ :=
    (LinearMap.toMatrixAlgEquiv T.basis).toRingHom.comp ContinuousLinearMap.toLinearMapRingHom
  let fL : (E →L[ℝ] E) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (LinearMap.toMatrix T.basis T.basis).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)
  let : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have he := adjointLinearMap_exponential hExp x 1
  rw [one_smul, hx, adjointLinearMap_one] at he
  simp only [one_smul] at he
  have hm : NormedSpace.exp M = 1 := by
    have hh := NormedSpace.map_exp f fL.continuous_of_finiteDimensional D
    change f (NormedSpace.exp D) = NormedSpace.exp M at hh
    rw [← he, map_one] at hh
    exact hh.symm
  have hM : M = 0 := (triangular_exp_eq_one_iff M (T.upper x)).mp hm
  have had : LieAlgebra.ad ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G) x = 0 := by
    apply (LinearMap.toMatrixAlgEquiv T.basis).injective
    exact hM.trans (map_zero _).symm
  change (LieAlgebra.ad ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G) x) y = 0
  rw [had]
  rfl

end PolycyclicRecognition

end

end OAI
