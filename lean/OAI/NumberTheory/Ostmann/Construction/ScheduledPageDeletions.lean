import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedInitialContradiction

namespace OAI

/-! # The two actual Page deletions fit the constructed initial prime pool -/
namespace Ostmann
open scoped Classical

noncomputable def pageDeletionPrimes (z : Option PrimitiveRealZero) (cutoff : ℕ) : Finset ℕ :=
  match z with
  | none => ∅
  | some z => (deletedConductorPrime z.modulus cutoff).toFinset

theorem pageDeletionPrimes_card (z : Option PrimitiveRealZero) (cutoff : ℕ) :
    (pageDeletionPrimes z cutoff).card ≤ 1 := by
  cases z with
  | none => simp [pageDeletionPrimes]
  | some z =>
    unfold pageDeletionPrimes
    cases h : deletedConductorPrime z.modulus cutoff <;> simp [h]

noncomputable def scheduledPageDeletions (P : PublishedProgressionInput) (L : ℝ)
    (cutoff : ℕ) : Finset ℕ :=
  pageDeletionPrimes (selectedPageZero P (giantProgressionCutoff L)) cutoff ∪
    pageDeletionPrimes (selectedPageZero P (bulkProgressionCutoff L)) cutoff

theorem scheduledPageDeletions_card (P : PublishedProgressionInput) (L : ℝ) (cutoff : ℕ) :
    (scheduledPageDeletions P L cutoff).card ≤ 2 := by
  exact (Finset.card_union_le _ _).trans (by
    have h₁ := pageDeletionPrimes_card (selectedPageZero P (giantProgressionCutoff L)) cutoff
    have h₂ := pageDeletionPrimes_card (selectedPageZero P (bulkProgressionCutoff L)) cutoff
    omega)

theorem scheduledPageDeletions_giant (P : PublishedProgressionInput) (L : ℝ) (cutoff : ℕ)
    (z : PrimitiveRealZero) (hz : selectedPageZero P (giantProgressionCutoff L) = some z)
    (p : ℕ) (hp : deletedConductorPrime z.modulus cutoff = some p) :
    p ∈ scheduledPageDeletions P L cutoff := by
  apply Finset.mem_union_left
  simp [pageDeletionPrimes, hz, hp]

theorem scheduledPageDeletions_bulk (P : PublishedProgressionInput) (L : ℝ) (cutoff : ℕ)
    (z : PrimitiveRealZero) (hz : selectedPageZero P (bulkProgressionCutoff L) = some z)
    (p : ℕ) (hp : deletedConductorPrime z.modulus cutoff = some p) :
    p ∈ scheduledPageDeletions P L cutoff := by
  apply Finset.mem_union_right
  simp [pageDeletionPrimes, hz, hp]

end Ostmann

end OAI
