import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealTorusContinuity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicAdjointExponential

namespace OAI

/-! # Compact Cartan rotations commute with the Cartan adjoint action -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) [H.IsCartanSubalgebra]

/-- A rotation fixing the Cartan algebra commutes with every Cartan bracket. -/
theorem realTorusOperator_cartan_bracket
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ, E)) G) H) (h : H)
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    realTorusOperator _ H z ⁅(h : GroupLieAlgebra (𝓘(ℝ, E)) G), x⁆ =
      ⁅(h : GroupLieAlgebra (𝓘(ℝ, E)) G), realTorusOperator _ H z x⁆ := by
  rw [realTorusOperator_lie, realTorusOperator_fixes_cartan]

/-- The same commutation holds for the exponential of the adjoint operator. -/
theorem realTorusOperator_commutes_adjoint_exponential
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ, E)) G) H) (h : H) (x : E) :
    realTorusOperator _ H z (NormedSpace.exp (groupAdjointOperator (E := E) (G := G) h) x) =
      NormedSpace.exp (groupAdjointOperator (E := E) (G := G) h)
        (realTorusOperator _ H z x) := by
  let A : E →L[ℝ] E := (realTorusOperator (GroupLieAlgebra (𝓘(ℝ, E)) G) H z).toContinuousLinearMap
  have hc : Commute A (groupAdjointOperator (E := E) (G := G) h) := by
    ext v
    exact realTorusOperator_cartan_bracket H z h v
  exact congrArg (fun f : E →L[ℝ] E => f x) (hc.exp_right.eq)

/-- In the original Lie group the compact rotations commute with conjugation
by exponentials of Cartan elements, at the tangent level. -/
theorem realTorusOperator_commutes_cartan_conjugation
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ, E)) G) H) (h : H) (x : E) :
    realTorusOperator _ H z (adjointLinearMap (E := E) (G := G) (Exp h) x) =
      adjointLinearMap (E := E) (G := G) (Exp h) (realTorusOperator _ H z x) := by
  have he := adjointLinearMap_exponential hExp (h : GroupLieAlgebra (𝓘(ℝ, E)) G) 1
  simp only [one_smul] at he
  rw [he]
  exact realTorusOperator_commutes_adjoint_exponential H z h x

end PolycyclicRecognition

end

end OAI
