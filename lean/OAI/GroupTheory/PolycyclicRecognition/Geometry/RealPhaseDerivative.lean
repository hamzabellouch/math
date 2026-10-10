import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexPhaseDerivative
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TangentRotationRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightRotationDerivation

namespace OAI

/-! # The real infinitesimal phase on the group model space -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold TensorProduct

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)) [H.IsCartanSubalgebra]

local instance : NormedAddCommGroup (ℂ ⊗[ℝ] GroupLieAlgebra (𝓘(ℝ,E)) G) :=
  ComplexCartan.rotationNormedAddCommGroup
local instance : NormedSpace ℂ (ℂ ⊗[ℝ] GroupLieAlgebra (𝓘(ℝ,E)) G) :=
  ComplexCartan.rotationNormedSpace
local instance : NormedSpace ℝ (ℂ ⊗[ℝ] GroupLieAlgebra (𝓘(ℝ,E)) G) :=
  { norm_smul_le := fun r x => by
      rw [← algebraMap_smul ℂ r x, norm_smul]
      simp }

theorem hasDerivAt_realPhase_line (h : H) (x : GroupLieAlgebra (𝓘(ℝ,E)) G) :
    HasDerivAt (fun t : ℝ =>
      (tangentTorusUnitAction H (realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H (t • h)) : E →L[ℝ] E) x)
      (show E from realImaginaryOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H h x) 0 := by
  let P : (ℂ ⊗[ℝ] GroupLieAlgebra (𝓘(ℝ,E)) G) →ₗ[ℝ] E :=
    complexificationRealPart (GroupLieAlgebra (𝓘(ℝ,E)) G)
  have hc := ComplexCartan.hasDerivAt_rotation_line
    (complexifiedSubalgebra (GroupLieAlgebra (𝓘(ℝ,E)) G) H)
    (realCartanInComplex (GroupLieAlgebra (𝓘(ℝ,E)) G) H h) ((1 : ℂ) ⊗ₜ[ℝ] x)
  have hd := P.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hc
  apply hd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t => by
    change _ = P (ComplexCartan.rotationLinear
      (complexifiedSubalgebra (GroupLieAlgebra (𝓘(ℝ,E)) G) H)
      (t • realCartanInComplex (GroupLieAlgebra (𝓘(ℝ,E)) G) H h) ((1 : ℂ) ⊗ₜ[ℝ] x))
    rw [← realCartanInComplex_real_smul]
    rfl)

end PolycyclicRecognition

end

end OAI
