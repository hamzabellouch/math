import OAI.Analysis.Pureness.Stabilization.MatrixCompression
import OAI.Analysis.Pureness.Stabilization.MatrixRestriction

namespace OAI
noncomputable section
open scoped ENNReal Topology CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma matrixMask_stage_range (n m : ℕ) (M : FinMatrix A m) :
    matrixStage m (matrixMask n M) ∈ Set.range (matrixStage (A := A) n) := by
  rcases le_total m n with h | h
  · refine ⟨matrixInclusion h M,?_⟩
    rw [matrixStage_compatible,matrixMask_eq_self h]
  · refine ⟨matrixRestrict h M,?_⟩
    rw [← matrixInclusion_restrict h M,matrixStage_compatible]

theorem matrixCompression_range (n : ℕ) (x : MatrixLimit A) :
    ∃ M : FinMatrix A n, matrixLimitStage n M = matrixCompression n x := by
  have hs : IsClosed (Set.range (matrixStage (A := A) n)) :=
    (matrixStage_isometry n).isClosedEmbedding.isClosed_range
  have hc : IsClosed ((matrixQuotientMask (A := A) n) ⁻¹' Set.range (matrixStage (A := A) n)) :=
    hs.preimage (matrixQuotientMaskCLM n).continuous
  have hsub : (matrixUnion A : Set (FamilyQuotient (FinMatrix A))) ⊆
      (matrixQuotientMask n) ⁻¹' Set.range (matrixStage (A := A) n) := by
    rintro y ⟨m,M,rfl⟩
    change matrixQuotientMask n (matrixStage m M) ∈ Set.range (matrixStage (A := A) n)
    rw [matrixQuotientMask_stage]
    exact matrixMask_stage_range n m M
  obtain ⟨M,hM⟩ := hc.closure_subset (closure_mono hsub x.2)
  exact ⟨M,Subtype.ext hM⟩

def matrixCornerExtract (n : ℕ) (x : MatrixLimit A) : FinMatrix A n :=
  (matrixCompression_range n x).choose

@[simp] theorem matrixCornerExtract_spec (n : ℕ) (x : MatrixLimit A) :
    matrixLimitStage n (matrixCornerExtract n x) = matrixCompression n x :=
  (matrixCompression_range n x).choose_spec

theorem matrixCornerExtract_norm_le (n : ℕ) (x : MatrixLimit A) : ‖matrixCornerExtract n x‖ ≤ ‖x‖ := by
  rw [← matrixLimitStage_norm n, matrixCornerExtract_spec]
  exact matrixCompression_norm_le n x

def matrixCornerExtractLinear (n : ℕ) : MatrixLimit A →ₗ[ℂ] FinMatrix A n where
  toFun := matrixCornerExtract n
  map_add' x y := by
    apply (matrixLimitStage_isometry n).injective
    simp only [map_add,matrixCornerExtract_spec]
  map_smul' c x := by
    apply (matrixLimitStage_isometry n).injective
    simp only [map_smul,matrixCornerExtract_spec,RingHom.id_apply]
end CuntzTrace

end

end OAI
