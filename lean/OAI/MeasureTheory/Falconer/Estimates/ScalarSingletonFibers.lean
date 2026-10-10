import OAI.MeasureTheory.Falconer.Estimates.ScalarPathLevel

namespace OAI

/-! Selecting a subset preserves one-leaf terminal fibers. -/
namespace Falconer.Regularization

 theorem scalar_singleton_fibers_mono {L Q : Finset (CellPath 1)} {a : ℕ}
    (hQL : Q ⊆ L)
    (hL : ∀ p ∈ L.image (List.take a), (prefixFiber L a p).card = 1) :
    ∀ p ∈ Q.image (List.take a), (prefixFiber Q a p).card = 1 := by
  classical
  intro p hp
  have hsub : prefixFiber Q a p ⊆ prefixFiber L a p := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨hQL (Finset.mem_filter.mp hq).1,(Finset.mem_filter.mp hq).2⟩
  have hcard := Finset.card_le_card hsub
  rw [hL p (Finset.image_subset_image hQL hp)] at hcard
  have hpos := (prefixFiber_nonempty hp).card_pos
  omega

end Falconer.Regularization

end OAI
