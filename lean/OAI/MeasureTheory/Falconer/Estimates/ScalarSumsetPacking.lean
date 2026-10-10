import OAI.MeasureTheory.Falconer.Estimates.ScalarBinaryGeometric

namespace OAI

/-! Separated original sums compared with the application-level
 Pluennecke estimate. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_separated_sumset_bound {δ K : ℝ} (hδ : 0 < δ)
    (A : Finset ℝ) (hA : A.Nonempty)
    (hsmall : ((scalarCells δ (A+A)).card:ℝ) ≤ K*(scalarCells δ A).card)
    (copies : ℕ) (E : Finset ℝ) (hE : E ⊆ copies • A)
    (hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ |x-y|) :
    (E.card:ℝ) ≤ (copies+2)*(2*K)^copies*(scalarCells δ A).card := by
  have hl : E.card ≤ (scalarCells δ (copies • A)).card := by
    rw [← Finset.card_image_of_injOn (scalarCells_injective hδ hsep)]
    exact Finset.card_le_card (Finset.image_subset_image hE)
  have hu := scalar_pluennecke δ A A hA hsmall copies 0
  simp only [zero_nsmul,sub_zero,add_zero,Nat.cast_zero] at hu
  exact (show (E.card:ℝ) ≤ ((scalarCells δ (copies • A)).card:ℝ) by exact_mod_cast hl).trans hu

end Falconer

end OAI
