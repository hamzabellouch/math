import OAI.Analysis.Pureness.Cuntz.FiniteMatrixLimit
import OAI.Analysis.Pureness.Completion.NonUnitalCStarCompletion

namespace OAI
noncomputable section
namespace CuntzPureness
open UniformSpace Function Topology
open UniformSpace.Completion
variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev CornerCompletion := Completion (FiniteMatrixLimit A)

instance cornerCompletionCStarAlgebra : NonUnitalCStarAlgebra (CornerCompletion A) := inferInstance

def completedMatrixInclude (k : ℕ) : MatrixStage A k →⋆ₙₐ[ℂ] CornerCompletion A where
  toFun a := (finiteMatrixInclude A k a : CornerCompletion A)
  map_zero' := by simp only [map_zero, coe_zero]
  map_add' a b := by simp only [map_add, coe_add]
  map_mul' a b := by simp only [map_mul, completion_coe_mul]
  map_smul' z a := by simp only [map_smul, coe_smul]; rfl
  map_star' a := by simp only [map_star, completion_coe_star]

lemma completedMatrixInclude_norm (k : ℕ) (a : MatrixStage A k) :
    ‖completedMatrixInclude A k a‖ = ‖a‖ := by
  change ‖(finiteMatrixInclude A k a : CornerCompletion A)‖ = _
  rw [norm_coe, finiteMatrixInclude_norm]

lemma completedMatrixInclude_isometry (k : ℕ) : Isometry (completedMatrixInclude A k) :=
  AddMonoidHomClass.isometry_of_norm _ (completedMatrixInclude_norm A k)

lemma completedMatrixInclude_corner {k l : ℕ} (h : k ≤ l) (a : MatrixStage A k) :
    completedMatrixInclude A l (corner h a) = completedMatrixInclude A k a := by
  change (finiteMatrixInclude A l (corner h a) : CornerCompletion A) = _
  rw [finiteMatrixInclude_corner]
  rfl

theorem completedMatrixInclude_dense :
    Dense (⋃ k : ℕ, Set.range (completedMatrixInclude A k)) := by
  have heq : (⋃ k : ℕ, Set.range (completedMatrixInclude A k)) =
      Set.range ((↑) : FiniteMatrixLimit A → CornerCompletion A) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨k, a, rfl⟩; exact ⟨finiteMatrixInclude A k a, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨k, a, rfl⟩ := DirectLimit.exists_eq_mk (matrixConnecting A) y
      exact ⟨k, a, rfl⟩
  rw [heq]
  exact denseRange_coe
end CuntzPureness

end

end OAI
