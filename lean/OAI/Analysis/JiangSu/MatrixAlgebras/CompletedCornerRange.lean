import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI

section

noncomputable section
namespace Pureness
open Filter Topology

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completedCompress_norm_le (k : ℕ) (a : CornerCompletion A) :
    ‖completedCompress A k a‖ ≤ ‖a‖ := by
  rw [← completedMatrixInclude_norm A k, include_completedCompress]
  exact completedCornerCut_norm_le A k a

lemma completedProjection_mul_include (k : ℕ) (a : MatrixStage A k) :
    completedProjection A k * completedMatrixInclude A k a = completedMatrixInclude A k a := by
  change completedMatrixInclude A k 1 * completedMatrixInclude A k a = _
  rw [← map_mul, one_mul]

lemma include_mul_completedProjection (k : ℕ) (a : MatrixStage A k) :
    completedMatrixInclude A k a * completedProjection A k = completedMatrixInclude A k a := by
  change completedMatrixInclude A k a * completedMatrixInclude A k 1 = _
  rw [← map_mul, mul_one]

lemma completedCornerCut_sandwich (k : ℕ) (a : MatrixStage A k) (v : CornerCompletion A) :
    completedCornerCut A k (star v * completedMatrixInclude A k a * v) =
      star (completedCornerCut A k v) * completedMatrixInclude A k a * completedCornerCut A k v := by
  simp only [completedCornerCut, star_mul, completedProjection_star, mul_assoc,
    completedProjection_mul_include]
  rw [← mul_assoc (completedMatrixInclude A k a) (completedProjection A k),
    include_mul_completedProjection]

lemma completedCompress_sandwich (k : ℕ) (a : MatrixStage A k) (v : CornerCompletion A) :
    completedCompress A k (star v * completedMatrixInclude A k a * v) =
      star (completedCompress A k v) * a * completedCompress A k v := by
  apply (completedMatrixInclude_isometry A k).injective
  rw [include_completedCompress, map_mul, map_mul, map_star, include_completedCompress,
    completedCornerCut_sandwich]

theorem cuntzSubequiv_completedMatrixInclude_iff (k : ℕ) (a b : MatrixStage A k) :
    CuntzSubequiv (completedMatrixInclude A k a) (completedMatrixInclude A k b) ↔ CuntzSubequiv a b := by
  constructor
  · intro hab
    obtain ⟨v, hv⟩ := (cuntzSubequiv_iff_sequence _ _).mp hab
    apply (cuntzSubequiv_iff_sequence _ _).mpr
    refine ⟨fun n => completedCompress A k (v n), ?_⟩
    simpa only [Function.comp_def, completedCompress_sandwich, completedCompress_include] using
      (completedCompress_continuous A k).continuousAt.tendsto.comp hv
  · intro hab
    obtain ⟨v, hv⟩ := (cuntzSubequiv_iff_sequence _ _).mp hab
    apply (cuntzSubequiv_iff_sequence _ _).mpr
    refine ⟨fun n => completedMatrixInclude A k (v n), ?_⟩
    simpa only [Function.comp_def, map_mul, map_star] using
      (completedMatrixInclude_isometry A k).continuous.continuousAt.tendsto.comp hv

end Pureness
end
end

end OAI
