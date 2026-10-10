import OAI.NumberTheory.Ostmann.Construction.ScheduledPageDeletions
import OAI.NumberTheory.Ostmann.Construction.ScheduledPrimeRanges
import OAI.NumberTheory.Ostmann.Construction.FrozenInitialSpectatorData

namespace OAI

namespace Ostmann
open scoped Classical

theorem selectedTailCellPrimes_avoids (A B : Set ℕ) (N hi : ℕ) (Y : ℝ)
    (D : Finset ℕ) (j p : ℕ) (hp : p ∈ D) :
    p ∉ selectedTailCellPrimes A B N Y hi D j := by
  intro h
  exact (Finset.mem_sdiff.mp h).2 hp

theorem completedCompensationSets_avoids (A B : Set ℕ) (N hi : ℕ) (Y : ℝ)
    (D : Finset ℕ) (top : ℕ) (cs : List ℕ) (p : ℕ) (hp : p ∈ D) (n : ℕ) :
    p ∉ completedCompensationSets A B N Y hi D top cs n :=
  selectedTailCellPrimes_avoids A B N hi Y D _ p hp

theorem scheduledRegularPrimeSets_avoids (A B : Set ℕ) (N hi : ℕ) (Y : ℝ)
    (D bulk : Finset ℕ) (hbulk : Disjoint bulk D) (top : ℕ) (cs : List ℕ)
    (n m p : ℕ) (hp : p ∈ D) (i : MovingRegularSlot n (scheduledSmallLength cs) m) :
    p ∉ scheduledRegularPrimeSets (selectedTailCellPrimes A B N Y hi D) bulk top cs n m i := by
  rcases i with ⟨u, i | i⟩
  · exact selectedTailCellPrimes_avoids A B N hi Y D _ p hp
  · exact fun h => Finset.disjoint_left.mp hbulk h hp

theorem selected_schedule_avoids_giant_page
    (P : PublishedProgressionInput) (A B : Set ℕ) (N hi : ℕ) (Y L : ℝ)
    (cutoff top : ℕ) (cs : List ℕ) (bulk : Finset ℕ)
    (hbulk : Disjoint bulk (scheduledPageDeletions P L cutoff))
    (z : PrimitiveRealZero) (hz : selectedPageZero P (giantProgressionCutoff L) = some z)
    (p : ℕ) (hp : deletedConductorPrime z.modulus cutoff = some p) :
    (∀ n, p ∉ completedCompensationSets A B N Y hi
      (scheduledPageDeletions P L cutoff) top cs n) ∧
    (∀ n m offset i, p ∉ scheduledRegularPrimeSets
      (selectedTailCellPrimes A B N Y hi (scheduledPageDeletions P L cutoff))
      bulk top (cs.drop offset) n m i) := by
  have hd := scheduledPageDeletions_giant P L cutoff z hz p hp
  exact ⟨completedCompensationSets_avoids A B N hi Y _ top cs p hd,
    fun n m offset i => scheduledRegularPrimeSets_avoids A B N hi Y _ bulk
      hbulk top (cs.drop offset) n m p hd i⟩

theorem FrozenInitialSpectatorData.avoids_giant_page
    {P : PublishedProgressionInput} {A : Set ℕ} {N d cutoff c₀ : ℕ}
    {p : Fin (d + d) → ℕ} {L ε : ℝ}
    (F : FrozenInitialSpectatorData A N p L ε c₀ (scheduledPageDeletions P L cutoff))
    (z : PrimitiveRealZero) (hz : selectedPageZero P (giantProgressionCutoff L) = some z)
    (q : ℕ) (hq : deletedConductorPrime z.modulus cutoff = some q) (i) : p i ≠ q := by
  intro h
  exact F.avoids i (h ▸ scheduledPageDeletions_giant P L cutoff z hz q hq)

theorem FrozenInitialSpectatorData.avoids_bulk_page
    {P : PublishedProgressionInput} {A : Set ℕ} {N d cutoff c₀ : ℕ}
    {p : Fin (d + d) → ℕ} {L ε : ℝ}
    (F : FrozenInitialSpectatorData A N p L ε c₀ (scheduledPageDeletions P L cutoff))
    (z : PrimitiveRealZero) (hz : selectedPageZero P (bulkProgressionCutoff L) = some z)
    (q : ℕ) (hq : deletedConductorPrime z.modulus cutoff = some q) (i) : p i ≠ q := by
  intro h
  exact F.avoids i (h ▸ scheduledPageDeletions_bulk P L cutoff z hz q hq)

end Ostmann

end OAI
