import OAI.NumberTheory.Jacobsthal.Paths.ActualTagFreezing
import OAI.NumberTheory.Jacobsthal.Primes.LargePrimeDeletion

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SurvivorResidueShift
open SievePartition LargePrimeDeletion

attribute [local instance] Classical.propDecidable

def successorResidues (a : ℕ → ℕ) (p : ℕ) : ℕ := a p+1

theorem residueBad_successor (a : ℕ → ℕ) (p i : ℕ) :
    residueBad (successorResidues a) p (i+1) ↔ residueBad a p i := by
  change Nat.ModEq p (i+1) (a p+1) ↔ Nat.ModEq p i (a p)
  exact ⟨Nat.ModEq.add_right_cancel' 1,Nat.ModEq.add_right 1⟩

theorem positive_survivors_image (Y z : ℕ) (a : ℕ → ℕ) :
    residueCandidates Y ∅ (cutoffPrimes z) (successorResidues a)=
      (cutoffSurvivors Y z a).image (fun i => i+1) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hn1,hnY,_hreq,havoid⟩ := mem_residueCandidates.mp hn
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    apply Finset.mem_image.mpr
    refine ⟨i,mem_cutoffSurvivors.mpr ⟨by omega,?_⟩,rfl⟩
    intro p hp hpz
    have hh := havoid p (mem_cutoffPrimes.mpr ⟨hp,hpz⟩)
    intro he
    exact hh ((residueBad_successor a p i).mpr he)
  · intro hn
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hiY,havoid⟩ := mem_cutoffSurvivors.mp hi
    apply mem_residueCandidates.mpr
    refine ⟨by omega,by omega,by simp,?_⟩
    intro p hp
    have hh := mem_cutoffPrimes.mp hp
    intro hb
    exact havoid p hh.1 hh.2 ((residueBad_successor a p i).mp hb)

theorem positive_survivors_card (Y z : ℕ) (a : ℕ → ℕ) :
    (residueCandidates Y ∅ (cutoffPrimes z) (successorResidues a)).card=
      (cutoffSurvivors Y z a).card := by
  rw [positive_survivors_image]
  apply Finset.card_image_iff.mpr
  intro i _hi j _hj he
  exact Nat.add_right_cancel he
end NumberTheoryLean.SurvivorResidueShift


end Erdos970

end OAI
