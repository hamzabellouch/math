import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicAdjointExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConjugationFlow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponential

namespace OAI

/-! # Intertwining the intrinsic adjoint action with matrix conjugation -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem lieHom_adjoint_exponential
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A)
    (x y : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    j (adjointLinearMap (E := E) (Exp x) y) =
      NormedSpace.exp (j x) * j y * NormedSpace.exp (-j x) := by
  let f : E →ₗ[ℝ] A := j.toLinearMap
  have he := exp_intertwine_apply f.toContinuousLinearMap
    (groupAdjointOperator (E := E) x) (adjointOperator (j x))
    (fun v => by
      change j ⁅x, v⁆ = j x * j v - j v * j x
      exact j.map_lie x v) y
  have hAd := adjointLinearMap_exponential hExp x 1
  simp only [one_smul] at hAd
  rw [hAd]
  exact he.trans (exp_adjointOperator_apply (j x) (j y))

end PolycyclicRecognition

end

end OAI
