import OAI.MeasureTheory.Falconer.Estimates.AllTestsRestoration
import OAI.MeasureTheory.Falconer.Estimates.RegularRoot

namespace OAI

/-! # The actual entry list is covered by the common restoration event -/

namespace Falconer
open Set

 theorem regularOuterList_subset_valid {d N : ℕ} (profile : ℝ → ℝ) {κ : ℝ}
    (hN : 0 < N) (hκ : 0 < κ) {c : ℕ} (hc : c ≤ N) :
    regularOuterList (d := d) profile N κ c ⊆ validDescriptors N := by
  intro b hb
  apply (mem_validDescriptors N b).mpr
  obtain rfl | hb := Finset.mem_insert.mp hb
  · exact ⟨Nat.zero_le c,hc⟩
  · exact policy_descriptor_valid _ (PlanarFalconer.sourcePolicyBlock_pos hN hκ) le_rfl
      (Finset.mem_filter.mp hb).1

end Falconer

end OAI
