import OAI.NumberTheory.Jacobsthal.Partitions.CrossingBandGeometry
import OAI.NumberTheory.Jacobsthal.Sieve.SurvivorResidueShift

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RootCutoffSurvivors
open SievePartition LargePrimeDeletion SurvivorResidueShift
open StoppedCountVertex StoppedCountAdapters LogarithmicBinPartition

attribute [local instance] Classical.propDecidable

theorem residue_survivors_union (Y : ℕ) (small P : Finset ℕ) (a : ℕ → ℕ) :
    survivors (residueCandidates Y ∅ small a) P (residueBad a)=residueCandidates Y ∅ (small∪P) a := by
  ext n
  constructor
  · intro hn
    obtain ⟨hn,hP⟩ := mem_survivors.mp hn
    obtain ⟨h1,hY,_hreq,hs⟩ := mem_residueCandidates.mp hn
    refine mem_residueCandidates.mpr ⟨h1,hY,by simp,?_⟩
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hs p hp
    · exact hP p hp
  · intro hn
    obtain ⟨h1,hY,_hreq,hboth⟩ := mem_residueCandidates.mp hn
    exact mem_survivors.mpr ⟨mem_residueCandidates.mpr ⟨h1,hY,by simp,
      fun p hp => hboth p (Finset.mem_union_left _ hp)⟩,
      fun p hp => hboth p (Finset.mem_union_right _ hp)⟩

theorem cutoffPrimes_eq_primesLE (z : ℕ) : cutoffPrimes z=Nat.primesLE z := by
  ext p
  simp only [mem_cutoffPrimes,Nat.mem_primesLE]
  exact and_comm

theorem source_cutoff_union {w top : ℝ} (hwt : w ≤ top) :
    cutoffPrimes ⌊w⌋₊∪sourcePrimeSet w top=cutoffPrimes ⌊top⌋₊ := by
  rw [cutoffPrimes_eq_primesLE,cutoffPrimes_eq_primesLE,sourcePrimeSet]
  have hs : Nat.primesLE ⌊w⌋₊ ⊆ Nat.primesLE ⌊top⌋₊ := by
    intro p hp
    obtain ⟨hbound,hprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hbound.trans (Nat.floor_mono hwt),hprime⟩
  ext p
  simp only [Finset.mem_union,Finset.mem_sdiff]
  constructor
  · rintro (hp | ⟨hp,_⟩)
    · exact hs hp
    · exact hp
  · intro hp
    by_cases hw : p∈Nat.primesLE ⌊w⌋₊
    · exact Or.inl hw
    · exact Or.inr ⟨hp,hw⟩

theorem root_count_eq_cutoff (Y : ℕ) {w top : ℝ} (hwt : w ≤ top)
    (a : ℕ → ℕ) (z : PrimeHistories.Node) (mu : ℝ) :
    countSurvivors Y (cutoffPrimes ⌊w⌋₊) (successorResidues a)
      (rootVertex z ∅ (sourcePrimeSet w top) mu)=
      ((cutoffSurvivors Y ⌊top⌋₊ a).card:ℝ) := by
  unfold countSurvivors
  change ((survivors (residueCandidates Y ∅ (cutoffPrimes ⌊w⌋₊) (successorResidues a))
    (sourcePrimeSet w top) (residueBad (successorResidues a))).card:ℝ)=_
  rw [residue_survivors_union,source_cutoff_union hwt,positive_survivors_card]

theorem cutoff_lower_of_root_lower (Y : ℕ) {w top S mu : ℝ} (hwt : w ≤ top)
    (z : PrimeHistories.Node)
    (hLower : ∀ a : ℕ → ℕ,S ≤ countSurvivors Y (cutoffPrimes ⌊w⌋₊) a
      (rootVertex z ∅ (sourcePrimeSet w top) mu)) :
    ∀ a : ℕ → ℕ,S ≤ ((cutoffSurvivors Y ⌊top⌋₊ a).card:ℝ) := by
  intro a
  simpa only [root_count_eq_cutoff Y hwt a z mu] using hLower (successorResidues a)
end NumberTheoryLean.RootCutoffSurvivors


end Erdos970

end OAI
