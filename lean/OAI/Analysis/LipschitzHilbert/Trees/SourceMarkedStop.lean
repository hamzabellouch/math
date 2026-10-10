import OAI.Analysis.LipschitzHilbert.Trees.SourceMarkedIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourceNodeMeasurable

namespace OAI

/-! Actual cell marks vanish after the first mass crossing, so passing
between the stopped prefix and the complete marked product is exact. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem source_marked_product_stop (n beta : ℕ → ℝ) (marked : ℕ → Prop)
    (count : ℕ) (M : ℝ) (hlast : n count ≤ M) (hanti : Antitone n)
    (hmarked : ∀ j < count, marked j → M < n j) :
    (∏ j ∈ Finset.range (firstMassStop n count M), if marked j then beta j else 1) =
      ∏ j ∈ Finset.range count, if marked j then beta j else 1 := by
  apply Finset.prod_subset (Finset.range_mono (firstMassStop_spec n count M hlast).1)
  intro j hj hnot
  have hstop : firstMassStop n count M ≤ j := by
    have : ¬j < firstMassStop n count M := by simpa only [Finset.mem_range] using hnot
    omega
  have hm : ¬marked j := fun hm =>
    (not_lt_of_ge (firstMassStop_after n count M hlast hanti hstop))
      (hmarked j (Finset.mem_range.mp hj) hm)
  exact ite_eq_right hm

/-- The exact mark tested at a point is the mark of its actual grid cell. -/
theorem reverseMarkedValue_eq_ite (grid : FiniteLineGrid) (level : ℕ → ℕ)
    (count : ℕ) (marked : ℕ → ℕ → Prop) (beta : ℕ → ℝ → ℝ) (j : ℕ) (x : ℝ) :
    reverseMarkedValue grid level count marked beta j x =
      if marked j (grid.index (level (ShiftedBlocks.reverseIndex count j)) x).val
        then beta j x else 1 := rfl

end LipschitzHilbert

end

end OAI
