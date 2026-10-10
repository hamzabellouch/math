import OAI.Analysis.Pureness.Completion.CompletedTraceWeight

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completedDiagonalWeight_cut (τ : TracialState A) (k : ℕ) (a : CornerCompletion A) (ha : 0 ≤ a) :
    completedDiagonalWeight τ (completedCornerCut A k a) = completedTraceValue τ k a := by
  rw [← include_completedCompress, completedDiagonalWeight_include τ k _ (completedCompress_nonneg k a ha)]
  rfl

lemma completedDiagonalWeight_cut_le (τ : TracialState A) (k : ℕ) (a : CornerCompletion A) (ha : 0 ≤ a) :
    completedDiagonalWeight τ (completedCornerCut A k a) ≤ completedDiagonalWeight τ a := by
  rw [completedDiagonalWeight_cut τ k a ha]
  exact le_iSup (fun k => completedTraceValue τ k a) k

lemma completedProjection_conjugate_le (k : ℕ) (x : CornerCompletion A) :
    x * completedProjection A k * star x ≤ x * star x := by
  have hq := completedProjection_mul_le (A := A) (k := k) le_rfl
  have he : (x - x * completedProjection A k) * star (x - x * completedProjection A k) =
      x * star x - x * completedProjection A k * star x := by
    simp only [star_sub, star_mul, completedProjection_star, sub_mul, mul_sub, mul_assoc]
    rw [← mul_assoc (completedProjection A k) (completedProjection A k), hq]
    noncomm_ring
  exact sub_nonneg.mp (he ▸ mul_star_self_nonneg (x - x * completedProjection A k))

lemma completedCornerCut_mono (k : ℕ) : Monotone (completedCornerCut A k) := by
  intro a b hab
  simpa only [completedCornerCut, completedProjection_star] using
    star_left_conjugate_le_conjugate hab (completedProjection A k)

lemma completedCornerCut_mul_star_le (k : ℕ) (x : CornerCompletion A) :
    completedCornerCut A k x * star (completedCornerCut A k x) ≤
      completedCornerCut A k (x * star x) := by
  have he : completedCornerCut A k x * star (completedCornerCut A k x) =
      completedCornerCut A k (x * completedProjection A k * star x) := by
    simp only [completedCornerCut, star_mul, completedProjection_star, mul_assoc]
    rw [← mul_assoc (completedProjection A k) (completedProjection A k), completedProjection_mul_le le_rfl]
  rw [he]
  exact completedCornerCut_mono k (completedProjection_conjugate_le k x)

lemma completedDiagonalWeight_finite_polar (τ : TracialState A) (k : ℕ) (x : MatrixStage A k) :
    completedDiagonalWeight τ (star (completedMatrixInclude A k x) * completedMatrixInclude A k x) =
      completedDiagonalWeight τ (completedMatrixInclude A k x * star (completedMatrixInclude A k x)) := by
  rw [← map_star, ← map_mul, ← map_mul,
    completedDiagonalWeight_include τ k _ (star_mul_self_nonneg _),
    completedDiagonalWeight_include τ k _ (mul_star_self_nonneg _), matrixTrace_tracial]

lemma completedDiagonalWeight_star_mul_le (τ : TracialState A) (x : CornerCompletion A) :
    completedDiagonalWeight τ (star x * x) ≤ completedDiagonalWeight τ (x * star x) := by
  have ht := completedCornerCut_tendsto A x
  apply completedDiagonalWeight_le_of_tendsto τ (ht.star.mul ht)
  intro k
  rw [← include_completedCompress, completedDiagonalWeight_finite_polar, include_completedCompress]
  exact (completedDiagonalWeight_mono τ (completedCornerCut_mul_star_le k x)).trans
    (completedDiagonalWeight_cut_le τ k (x * star x) (mul_star_self_nonneg x))

theorem completedDiagonalWeight_tracial (τ : TracialState A) (x : CornerCompletion A) :
    completedDiagonalWeight τ (star x * x) = completedDiagonalWeight τ (x * star x) := by
  apply le_antisymm (completedDiagonalWeight_star_mul_le τ x)
  simpa only [star_star] using completedDiagonalWeight_star_mul_le τ (star x)
end CuntzPureness

end

end OAI
