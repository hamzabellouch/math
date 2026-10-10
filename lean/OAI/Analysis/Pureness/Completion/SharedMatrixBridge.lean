import OAI.Analysis.Pureness.Completion.CompletedCompressions
import OAI.Analysis.Pureness.Stabilization.MatrixLimitLift

namespace OAI
noncomputable section
namespace CuntzPureness
open Topology
variable {A : Type*} [CStarAlgebra A]

lemma shared_matrixSuccessor_eq_corner (k : ℕ) (a : MatrixStage A k) :
    CuntzTrace.matrixSuccessor k a = corner (Nat.le_succ k) a := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [corner]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [corner]
    · simp [corner, i.isLt, j.isLt]

lemma shared_matrixInclusion_eq_corner {k l : ℕ} (h : k ≤ l) (a : MatrixStage A k) :
    CuntzTrace.matrixInclusion h a = corner h a := by
  change CuntzTrace.matrixPad h a = _
  induction l, h using Nat.le_induction with
  | base => simp
  | succ l h ih =>
    rw [CuntzTrace.matrixPad_succ h, ih, shared_matrixSuccessor_eq_corner, corner_comp]

variable [PartialOrder A] [StarOrderedRing A]

lemma completedMatrixInclude_shared_compatible {k l : ℕ} (h : k ≤ l) (a : MatrixStage A k) :
    completedMatrixInclude A l (CuntzTrace.matrixInclusion h a) = completedMatrixInclude A k a := by
  rw [shared_matrixInclusion_eq_corner, completedMatrixInclude_corner]

def sharedMatrixToCompletion : CuntzTrace.MatrixLimit A →⋆ₙₐ[ℂ] CornerCompletion A :=
  CuntzTrace.matrixLimitLift (completedMatrixInclude A) completedMatrixInclude_shared_compatible

@[simp] lemma sharedMatrixToCompletion_stage (k : ℕ) (a : MatrixStage A k) :
    sharedMatrixToCompletion (CuntzTrace.matrixLimitStage k a) = completedMatrixInclude A k a :=
  CuntzTrace.matrixLimitLift_stage _ _ k a

lemma sharedMatrixToCompletion_continuous : Continuous (sharedMatrixToCompletion (A := A)) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul] using
    NonUnitalStarAlgHom.norm_apply_le (sharedMatrixToCompletion (A := A)) (x-y)

lemma sharedMatrixToCompletion_norm (x : CuntzTrace.MatrixLimit A) :
    ‖sharedMatrixToCompletion x‖ = ‖x‖ := by
  refine CuntzTrace.finiteMatrixSubalgebra_dense.induction_on x ?_ ?_
  · exact isClosed_eq (sharedMatrixToCompletion_continuous.norm) continuous_norm
  · intro y
    obtain ⟨k,a,rfl⟩ := CuntzTrace.finiteMatrixStage_surjective y
    change ‖sharedMatrixToCompletion (CuntzTrace.matrixLimitStage k a)‖ =
      ‖CuntzTrace.matrixLimitStage k a‖
    rw [sharedMatrixToCompletion_stage, completedMatrixInclude_norm, CuntzTrace.matrixLimitStage_norm]

lemma sharedMatrixToCompletion_isometry : Isometry (sharedMatrixToCompletion (A := A)) :=
  AddMonoidHomClass.isometry_of_norm _ sharedMatrixToCompletion_norm

lemma sharedMatrixToCompletion_surjective : Function.Surjective (sharedMatrixToCompletion (A := A)) := by
  intro x
  have hc : IsClosed (Set.range (sharedMatrixToCompletion (A := A))) :=
    (sharedMatrixToCompletion_isometry (A := A)).isClosedEmbedding.isClosed_range
  have hd : Dense (Set.range (sharedMatrixToCompletion (A := A))) := by
    apply (completedMatrixInclude_dense A).mono
    rintro y hy
    obtain ⟨k,a,rfl⟩ := Set.mem_iUnion.mp hy
    exact ⟨CuntzTrace.matrixLimitStage k a, sharedMatrixToCompletion_stage k a⟩
  have hx := hd x
  rw [hc.closure_eq] at hx
  exact hx

def sharedMatrixEquiv : CuntzTrace.MatrixLimit A ≃⋆ₐ[ℂ] CornerCompletion A :=
  StarAlgEquiv.ofBijective sharedMatrixToCompletion
    ⟨sharedMatrixToCompletion_isometry.injective, sharedMatrixToCompletion_surjective⟩

@[simp] theorem sharedMatrixEquiv_stage (k : ℕ) (a : MatrixStage A k) :
    sharedMatrixEquiv (CuntzTrace.matrixLimitStage k a) = completedMatrixInclude A k a :=
  sharedMatrixToCompletion_stage k a
end CuntzPureness

end

end OAI
