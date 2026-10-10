import OAI.NumberTheory.Jacobsthal.Partitions.FiniteWeightedChoiceBox
import OAI.NumberTheory.Jacobsthal.Primes.PrimeChoiceCoordinateMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SingletonSubsetMass
open PrimeBinAlignmentMass

attribute [local instance] Classical.propDecidable

noncomputable def subsetWeight (s : Finset ℕ) : ℝ := ∏ p ∈ s,(p:ℝ)⁻¹

theorem subsetWeight_nonnegative (s : Finset ℕ) : 0 ≤ subsetWeight s :=
  Finset.prod_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))

theorem singleton_total_mass (P : Finset ℕ) :
    (∑ s ∈ P.powersetCard 1,subsetWeight s)=mass P := by
  rw [Finset.powersetCard_one,Finset.sum_map]
  simp [subsetWeight,mass]

theorem all_filter_powerset (P : Finset ℕ) (k : ℕ) (E : ℕ → Prop) :
    (P.powersetCard k).filter (fun s => ∀ p ∈ s,E p)=(P.filter E).powersetCard k := by
  ext s
  simp only [Finset.mem_filter,Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hsub,hcard⟩,he⟩
    refine ⟨?_,hcard⟩
    intro p hp
    exact Finset.mem_filter.mpr ⟨hsub hp,he p hp⟩
  · rintro ⟨hsub,hcard⟩
    refine ⟨⟨?_,hcard⟩,?_⟩
    · intro p hp
      exact (Finset.mem_filter.mp (hsub hp)).1
    · intro p hp
      exact (Finset.mem_filter.mp (hsub hp)).2

theorem some_filter_singletons (P : Finset ℕ) (E : ℕ → Prop) :
    (P.powersetCard 1).filter (fun s => ∃ p ∈ s,E p)=(P.filter E).powersetCard 1 := by
  rw [← all_filter_powerset P 1 E]
  apply Finset.filter_congr
  intro s hs
  obtain ⟨p,rfl⟩ := Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hs).2
  simp

theorem singleton_all_mass (P : Finset ℕ) (E : ℕ → Prop) :
    (∑ s ∈ (P.powersetCard 1).filter (fun s => ∀ p ∈ s,E p),subsetWeight s)=mass (P.filter E) := by
  rw [all_filter_powerset,singleton_total_mass]

theorem singleton_some_mass (P A : Finset ℕ) (hA : A ⊆ P) :
    (∑ s ∈ (P.powersetCard 1).filter (fun s => ∃ p ∈ s,p ∈ A),subsetWeight s)=mass A := by
  calc
    _ = ∑ s ∈ A.powersetCard 1,subsetWeight s := by
      apply Finset.sum_congr
      · ext s
        simp only [Finset.mem_filter,Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨_hSP,hcard⟩,hex⟩
          obtain ⟨p,rfl⟩ := Finset.card_eq_one.mp hcard
          simp only [Finset.mem_singleton,exists_eq_left] at hex
          exact ⟨Finset.singleton_subset_iff.mpr hex,by simp⟩
        · rintro ⟨hSA,hcard⟩
          obtain ⟨p,rfl⟩ := Finset.card_eq_one.mp hcard
          have hpA := hSA (by simp : p ∈ ({p} : Finset ℕ))
          exact ⟨⟨fun q hq => hA (hSA hq),by simp⟩,p,by simp,hpA⟩
      · intro s _hs
        rfl
    _ = _ := singleton_total_mass A

end NumberTheoryLean.SingletonSubsetMass


end Erdos970

end OAI
