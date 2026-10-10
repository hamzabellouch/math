import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactFiniteDimensionalHull
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation

namespace OAI

/-! # A uniformly positive separator for the compact bad-character set -/

noncomputable section
namespace PolycyclicRecognition
open scoped InnerProductSpace
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_inner_separator_of_compact_no_convex_zero {C : Set E}
    (hC : IsCompact C) (hzero : (0 : E) ∉ convexHull ℝ C) :
    ∃ v : E, ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ C, δ < ⟪v, x⟫_ℝ := by
  obtain ⟨f, δ, hδ, hf⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ C) (compact_finiteDimensional_convexHull hC).isClosed hzero
  refine ⟨(InnerProductSpace.toDual ℝ E).symm f, δ, ?_, ?_⟩
  · simpa only [map_zero] using hδ
  · intro x hx
    rw [InnerProductSpace.toDual_symm_apply]
    exact hf x (subset_convexHull ℝ C hx)

end PolycyclicRecognition

end

end OAI
