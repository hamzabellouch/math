import OAI.Analysis.Pureness.Completion.CompletedCornerRange
import OAI.Analysis.Pureness.Operators.StarHomOrderReflection
import OAI.Analysis.Pureness.Cuntz.CuntzRankMonotone

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {k l : ℕ}

lemma compress_nonneg (h : k ≤ l) (a : MatrixStage A l) (ha : 0 ≤ a) : 0 ≤ compress h a := by
  apply (nonUnitalStarAlgHom_nonneg_iff (cornerHom h) (corner_injective h) _).mp
  change 0 ≤ corner h (compress h a)
  rw [corner_compress]
  simpa only [cornerProjection_star] using star_left_conjugate_nonneg ha (cornerProjection (A := A) h)

lemma matrixRank_compress_le [NeZero k] [NeZero l] (τ : TracialState A) (h : k ≤ l)
    (a : MatrixStage A l) (ha : 0 ≤ a) : matrixRank τ (compress h a) ≤ matrixRank τ a := by
  rw [← matrixRank_corner τ h _ (compress_nonneg h a ha)]
  unfold matrixRank
  gcongr
  exact (corner_compress_cuntz h a).rank_le
    (corner_nonneg h _ (compress_nonneg h a ha)) ha (matrixTracialState τ)

lemma matrixTrace_compress_le (τ : TracialState A) (h : k ≤ l) (a : MatrixStage A l) (ha : 0 ≤ a) :
    matrixTrace τ (compress h a) ≤ matrixTrace τ a := by
  rw [← matrixTrace_corner τ h, matrixTrace_apply, matrixTrace_apply]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.val < k
  · simp [corner, compress, hi]
  · simp only [corner_row_zero h _ i i hi, map_zero]
    exact τ.functional.map_nonneg (matrix_entry_nonneg a ha i)

lemma completedCompress_nonneg (k : ℕ) (a : CornerCompletion A) (ha : 0 ≤ a) :
    0 ≤ completedCompress A k a := by
  apply (nonUnitalStarAlgHom_nonneg_iff (completedMatrixInclude A k)
    (completedMatrixInclude_isometry A k).injective _).mp
  rw [include_completedCompress]
  exact completedCornerCut_nonneg A k a ha

lemma completedProjection_mul_le (h : k ≤ l) :
    completedProjection A k * completedProjection A l = completedProjection A k := by
  change completedMatrixInclude A k 1 * completedMatrixInclude A l 1 = _
  rw [← completedMatrixInclude_corner A h 1, ← map_mul, mul_one, completedMatrixInclude_corner]
  rfl

lemma completedProjection_mul_ge (h : k ≤ l) :
    completedProjection A l * completedProjection A k = completedProjection A k := by
  change completedMatrixInclude A l 1 * completedMatrixInclude A k 1 = _
  rw [← completedMatrixInclude_corner A h 1, ← map_mul, one_mul, completedMatrixInclude_corner]
  rfl

lemma completedCornerCut_nested (h : k ≤ l) (a : CornerCompletion A) :
    completedCornerCut A k (completedCornerCut A l a) = completedCornerCut A k a := by
  dsimp [completedCornerCut]
  calc
    _ = (completedProjection A k * completedProjection A l) * a *
        (completedProjection A l * completedProjection A k) := by simp only [mul_assoc]
    _ = _ := by rw [completedProjection_mul_le h, completedProjection_mul_ge h]

lemma completedCornerCut_include (h : k ≤ l) (a : MatrixStage A l) :
    completedCornerCut A k (completedMatrixInclude A l a) = completedMatrixInclude A k (compress h a) := by
  rw [completedCornerCut, completedProjection, ← completedMatrixInclude_corner A h 1,
    ← map_mul, ← map_mul, ← cornerProjection_eq h, ← corner_compress, completedMatrixInclude_corner]

theorem completedCompress_compat (h : k ≤ l) (a : CornerCompletion A) :
    compress h (completedCompress A l a) = completedCompress A k a := by
  apply (completedMatrixInclude_isometry A k).injective
  rw [← completedCornerCut_include, include_completedCompress, completedCornerCut_nested h,
    include_completedCompress]

lemma completedCompression_trace_monotone (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    Monotone (fun k : ℕ => matrixTrace τ (completedCompress A k a)) := by
  intro k l h
  dsimp only
  rw [← completedCompress_compat h a]
  exact matrixTrace_compress_le τ h _ (completedCompress_nonneg l a ha)

lemma completedCompression_rank_monotone (τ : TracialState A) (a : CornerCompletion A) (ha : 0 ≤ a) :
    Monotone (fun k : ℕ => matrixRank τ (completedCompress A (k + 1) a)) := by
  intro k l h
  dsimp only
  rw [← completedCompress_compat (Nat.add_le_add_right h 1) a]
  exact matrixRank_compress_le τ _ _ (completedCompress_nonneg _ a ha)
end CuntzPureness

end

end OAI
