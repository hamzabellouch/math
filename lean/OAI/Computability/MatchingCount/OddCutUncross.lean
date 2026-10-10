import OAI.Computability.MatchingCount.OddCutParity

namespace OAI

section

namespace BinaryMatching.OddCutUncross
open Finset UnitFlow CutAlgebra TerminalMincut OddCutParity
variable {n : ℕ}

lemma separates_compl (U A : Finset (Fin n)) (hA : Separates U A) : Separates U Aᶜ := by
  obtain ⟨a,ha,z,hz,haa,hza⟩ := hA
  exact ⟨z,hz,a,ha,mem_compl.mpr hza,by simpa using haa⟩

lemma uncross_on_side (c : Fin n → Fin n → ℕ) (hc : ∀ i j, c i j=c j i)
    (U A S : Finset (Fin n)) (hsep : Separates U A) (heven : Even (A∩U).card)
    (hmin : ∀ T, Separates U T → cutCapacity c A ≤ cutCapacity c T)
    (hinside : OddSide (A∩U) S) :
    ∃ T, T⊆A ∧ OddSide U T ∧ cutCapacity c T ≤ cutCapacity c S := by
  obtain ⟨a,ha,b,hb,haa,hba⟩ := hsep
  have horient : ∃ S', OddSide (A∩U) S' ∧ cutCapacity c S'=cutCapacity c S ∧
      ∃ z∈U, z∉A ∧ z∉S' := by
    by_cases hex : ∃ z∈U, z∉A ∧ z∉S
    · exact ⟨S,hinside,rfl,hex⟩
    · have hbS : b∈S := by
        by_contra hh
        exact hex ⟨b,hb,hba,hh⟩
      exact ⟨Sᶜ,odd_other (A∩U) S heven hinside,cut_compl c hc S,
        b,hb,hba,by simpa using hbS⟩
  obtain ⟨S',hodd,hcap,z,hz,hza,hzs⟩ := horient
  have hunion : Separates U (S'∪A) :=
    ⟨a,ha,z,hz,mem_union_right _ haa,by simpa only [mem_union,not_or] using And.intro hzs hza⟩
  have hlow := hmin (S'∪A) hunion
  have hsub := cut_submodular c S' A
  refine ⟨S'∩A,inter_subset_right,?_,?_⟩
  · simpa only [OddSide,inter_assoc] using hodd
  · omega

end BinaryMatching.OddCutUncross
end

end OAI
