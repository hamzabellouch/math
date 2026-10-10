import OAI.Analysis.Pureness.Completion.CompletedCompressions

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completedCornerCut_finite_range (k l : ℕ) (a : MatrixStage A l) :
    completedCornerCut A k (completedMatrixInclude A l a) ∈ Set.range (completedMatrixInclude A k) := by
  let m := max k l
  have hk : k ≤ m := le_max_left _ _
  have hl : l ≤ m := le_max_right _ _
  refine ⟨compress hk (corner hl a), ?_⟩
  rw [completedCornerCut, completedProjection, ← completedMatrixInclude_corner A hk 1,
    ← completedMatrixInclude_corner A hl a, ← map_mul, ← map_mul,
    ← cornerProjection_eq hk, ← corner_compress, completedMatrixInclude_corner]

theorem completedCornerCut_mem_range (k : ℕ) (a : CornerCompletion A) :
    completedCornerCut A k a ∈ Set.range (completedMatrixInclude A k) := by
  have hc : IsClosed {a : CornerCompletion A |
      completedCornerCut A k a ∈ Set.range (completedMatrixInclude A k)} :=
    (completedMatrixInclude_isometry A k).isClosedEmbedding.isClosed_range.preimage
      (completedCornerCut_continuous A k)
  apply hc.closure_subset_iff.mpr ?_ (completedMatrixInclude_dense A a)
  intro b hb
  obtain ⟨l, c, rfl⟩ := Set.mem_iUnion.mp hb
  exact completedCornerCut_finite_range A k l c

def completedCompress (k : ℕ) (a : CornerCompletion A) : MatrixStage A k :=
  Classical.choose (completedCornerCut_mem_range A k a)

@[simp] lemma include_completedCompress (k : ℕ) (a : CornerCompletion A) :
    completedMatrixInclude A k (completedCompress A k a) = completedCornerCut A k a :=
  Classical.choose_spec (completedCornerCut_mem_range A k a)

lemma completedCompress_continuous (k : ℕ) : Continuous (completedCompress A k) := by
  apply (completedMatrixInclude_isometry A k).isEmbedding.isInducing.continuous_iff.mpr
  simpa only [Function.comp_def, include_completedCompress] using completedCornerCut_continuous A k

lemma completedCompress_norm_le (k : ℕ) (a : CornerCompletion A) :
    ‖completedCompress A k a‖ ≤ ‖a‖ := by
  rw [← completedMatrixInclude_norm A k, include_completedCompress]
  exact completedCornerCut_norm_le A k a

@[simp] lemma completedCompress_include (k : ℕ) (a : MatrixStage A k) :
    completedCompress A k (completedMatrixInclude A k a) = a := by
  apply (completedMatrixInclude_isometry A k).injective
  rw [include_completedCompress, completedCornerCut_fixes A le_rfl]

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
  rw [← mul_assoc (completedMatrixInclude A k a) (completedProjection A k), include_mul_completedProjection]

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
    have ht := (completedCompress_continuous A k).continuousAt.tendsto.comp hv
    simpa only [Function.comp_def, completedCompress_sandwich, completedCompress_include] using ht
  · intro hab
    obtain ⟨v, hv⟩ := (cuntzSubequiv_iff_sequence _ _).mp hab
    apply (cuntzSubequiv_iff_sequence _ _).mpr
    refine ⟨fun n => completedMatrixInclude A k (v n), ?_⟩
    have ht := (completedMatrixInclude_isometry A k).continuous.continuousAt.tendsto.comp hv
    simpa only [Function.comp_def, map_mul, map_star] using ht
end CuntzPureness

end

end OAI
