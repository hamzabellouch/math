import OAI.Analysis.Pureness.Completion.CompletedSpatialBridge
import OAI.Analysis.Pureness.Completion.CompletedSharedTrace
import OAI.Analysis.Pureness.Comparison.SpatialTrace

namespace OAI
noncomputable section
open scoped CStarAlgebra ENNReal
namespace CuntzPureness
open CuntzTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem shared_completedCompress (n : ℕ) (x : CuntzTrace.MatrixLimit A) :
    completedCompress A n (sharedMatrixEquiv x) = CuntzTrace.matrixCornerExtract n x := by
  apply (completedMatrixInclude_isometry A n).injective
  rw [include_completedCompress, ← sharedMatrixEquiv_stage,
    CuntzTrace.matrixCornerExtract_spec, CuntzComparison.matrixCompression_eq_corner]
  simp only [completedCornerCut, completedProjection, CuntzComparison.matrixCornerProjection,
    map_mul, sharedMatrixEquiv_stage]

lemma shared_matrixTraceLinear (τ : TracialState A) (n : ℕ) (M : MatrixStage A n) :
    τ.toShared.matrixTraceLinear M = matrixTrace τ M := rfl

theorem shared_matrixExtendedTrace_eq (τ : TracialState A) :
    τ.toShared.matrixExtendedTrace = sharedExtendedTrace τ := by
  ext a
  change (⨆ n : ℕ, ENNReal.ofReal (τ.toShared.matrixCornerFunctional n a.1).re) =
    ⨆ n : ℕ, completedTraceValue τ n (sharedMatrixEquiv a.1)
  apply iSup_congr
  intro n
  rw [CuntzComparison.TracialState.matrixCornerFunctional_apply, shared_matrixTraceLinear]
  unfold completedTraceValue
  rw [shared_completedCompress]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : Function.Injective π)

lemma completedSpatial_inverse (x : CornerCompletion A) :
    CuntzComparison.spatialInverse π hπ (completedSpatialEquiv π hπ x) = sharedMatrixEquiv.symm x :=
  (CuntzComparison.spatialEquiv π hπ).symm_apply_apply _

theorem spatialTrace_completed (τ : TracialState A) (a : Positive (CornerCompletion A)) :
    τ.toShared.spatialTrace π hπ (Positive.map (completedSpatialEquiv π hπ).toNonUnitalStarAlgHom a) =
      completedDiagonalWeight τ a.1 := by
  change τ.toShared.matrixExtendedTrace
    (Positive.map (CuntzComparison.spatialInverse π hπ)
      (Positive.map (completedSpatialEquiv π hπ).toNonUnitalStarAlgHom a)) = _
  rw [shared_matrixExtendedTrace_eq]
  change completedDiagonalWeight τ (sharedMatrixEquiv
    (CuntzComparison.spatialInverse π hπ (completedSpatialEquiv π hπ a.1))) = _
  rw [completedSpatial_inverse, StarAlgEquiv.apply_symm_apply]

theorem spatialRank_completed (τ : TracialState A) (a : Positive (CornerCompletion A)) :
    (τ.toShared.spatialTrace π hπ).rank
      (Positive.map (completedSpatialEquiv π hπ).toNonUnitalStarAlgHom a) = completedRootRank τ a.1 := by
  have ht : (τ.toShared.spatialTrace π hπ).pullback
      (completedSpatialEquiv π hπ).toNonUnitalStarAlgHom = completedExtendedTrace τ := by
    ext b
    exact spatialTrace_completed π hπ τ b
  rw [← ExtendedTrace.rank_pullback, ht, completedExtendedTrace_rank]
end CuntzPureness

end

end OAI
