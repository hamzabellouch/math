import OAI.Analysis.Pureness.Completion.SharedMatrixBridge
import OAI.Analysis.Pureness.Comparison.SpatialIdentification

namespace OAI
open scoped CStarAlgebra
noncomputable section
namespace CuntzPureness
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : Function.Injective π)

def completedSpatialEquiv : CornerCompletion A ≃⋆ₐ[ℂ] CuntzComparison.SpatialStabilization π :=
  sharedMatrixEquiv.symm.trans (CuntzComparison.spatialEquiv π hπ)

@[simp] theorem completedSpatialEquiv_stage (k : ℕ) (a : MatrixStage A k) :
    completedSpatialEquiv π hπ (completedMatrixInclude A k a) =
      CuntzComparison.spatialStage π k a := by
  have hx : sharedMatrixEquiv.symm (completedMatrixInclude A k a) = CuntzTrace.matrixLimitStage k a :=
    (congrArg sharedMatrixEquiv.symm (sharedMatrixEquiv_stage k a).symm).trans
      (sharedMatrixEquiv.symm_apply_apply _)
  exact congrArg (CuntzComparison.spatialEquiv π hπ) hx

@[simp] theorem completedSpatialEquiv_norm (x : CornerCompletion A) :
    ‖completedSpatialEquiv π hπ x‖ = ‖x‖ :=
  by
    change ‖CuntzComparison.spatialEquiv π hπ (sharedMatrixEquiv.symm x)‖ = ‖x‖
    rw [CuntzComparison.spatialEquiv_norm]
    have h := sharedMatrixToCompletion_norm (sharedMatrixEquiv.symm x)
    change ‖sharedMatrixEquiv (sharedMatrixEquiv.symm x)‖ = ‖sharedMatrixEquiv.symm x‖ at h
    rw [StarAlgEquiv.apply_symm_apply] at h
    exact h.symm

theorem completedSpatialEquiv_cut (k : ℕ) (x : CornerCompletion A) :
    completedSpatialEquiv π hπ (completedCornerCut A k x) =
      CuntzComparison.spatialStage π k 1 * completedSpatialEquiv π hπ x *
        CuntzComparison.spatialStage π k 1 := by
  simp only [completedCornerCut, completedProjection, map_mul, completedSpatialEquiv_stage]

def TracialState.toShared (τ : TracialState A) : CuntzComparison.TracialState A where
  toPositiveLinearMap := τ.functional
  normalized := τ.normalized
  tracial := τ.tracial

theorem TracialState.source_gns_injective (τ : TracialState A) (hsimple : TopologicallySimple A) :
    Function.Injective τ.functional.gnsNonUnitalStarAlgHom := by
  apply CuntzComparison.faithful_gns_injective τ.functional
  intro a ha
  exact (CStarRing.star_mul_self_eq_zero_iff a).mp
    (τ.faithful hsimple (star a*a) (star_mul_self_nonneg a) ha)

def TracialState.completedSpatialEquiv (τ : TracialState A) (hsimple : TopologicallySimple A) :
    CornerCompletion A ≃⋆ₐ[ℂ]
      CuntzComparison.SpatialStabilization τ.functional.gnsNonUnitalStarAlgHom :=
  CuntzPureness.completedSpatialEquiv τ.functional.gnsNonUnitalStarAlgHom (τ.source_gns_injective hsimple)
end CuntzPureness

end

end OAI
