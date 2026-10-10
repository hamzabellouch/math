import Mathlib
import OAI.Analysis.Commutator.EqualProjectionPartition
import OAI.Analysis.Commutator.PartitionRankComparison

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

local instance partitionRankDecidableEq : DecidableEq ι := Classical.decEq ι

def rank (e : H →L[ℂ] H) : ℕ := by
  classical
  exact Nat.findGreatest (fun k => ∃ s : Finset ι,s.card=k ∧ SubEquivalent M (D.part s) e)
    (Fintype.card ι)

lemma rank_le_card (e : H →L[ℂ] H) : D.rank e≤Fintype.card ι := by
  classical
  exact Nat.findGreatest_le _

lemma exists_rank (e : H →L[ℂ] H) (he : IsStarProjection e) :
    ∃ s : Finset ι,s.card=D.rank e ∧ SubEquivalent M (D.part s) e := by
  classical
  apply Nat.findGreatest_spec (P := fun k => ∃ s : Finset ι, s.card=k ∧ SubEquivalent M (D.part s) e)
    (Nat.zero_le (Fintype.card ι))
  exact ⟨∅,by simp,by simpa only [D.part_empty] using
    subEquivalent_of_le M.zero_mem (IsStarProjection.zero _) he.nonneg⟩

lemma card_le_rank_of_subEquivalent {e : H →L[ℂ] H} (s : Finset ι)
    (h : SubEquivalent M (D.part s) e) : s.card≤D.rank e := by
  classical
  exact Nat.le_findGreatest (Finset.card_le_univ s) ⟨s,rfl,h⟩

lemma part_subEquivalent_of_card_le_rank {e : H →L[ℂ] H} (he : IsStarProjection e)
    (s : Finset ι) (hs : s.card≤D.rank e) : SubEquivalent M (D.part s) e := by
  obtain ⟨t,ht,hte⟩ := D.exists_rank e he
  exact (D.part_subEquivalent_of_card_le s t (ht ▸ hs)).trans
    (D.part_projection s) (D.part_projection t) hte

lemma part_subEquivalent_iff_card_le_rank {e : H →L[ℂ] H} (he : IsStarProjection e)
    (s : Finset ι) : SubEquivalent M (D.part s) e ↔ s.card≤D.rank e :=
  ⟨D.card_le_rank_of_subEquivalent s,D.part_subEquivalent_of_card_le_rank he s⟩

lemma rank_mono_subEquivalent {e f : H →L[ℂ] H}
    (he : IsStarProjection e) (h : SubEquivalent M e f) : D.rank e≤D.rank f := by
  obtain ⟨s,hs,hse⟩ := D.exists_rank e he
  rw [←hs]
  exact D.card_le_rank_of_subEquivalent s (hse.trans (D.part_projection s) he h)

lemma rank_congr_equivalent {e f : H →L[ℂ] H}
    (he : IsStarProjection e) (hf : IsStarProjection f) (h : Equivalent M e f) : D.rank e=D.rank f :=
  Nat.le_antisymm (D.rank_mono_subEquivalent he h.subEquivalent)
    (D.rank_mono_subEquivalent hf h.symm.subEquivalent)

lemma rank_mono {e f : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e) (hef : e≤f) :
    D.rank e≤D.rank f := D.rank_mono_subEquivalent he (subEquivalent_of_le heM he hef)

lemma rank_part [Nontrivial H] (hfin : IsFiniteAlgebra M) (s : Finset ι) : D.rank (D.part s)=s.card := by
  obtain ⟨t,ht,hts⟩ := D.exists_rank (D.part s) (D.part_projection s)
  apply Nat.le_antisymm
  · rw [←ht]
    exact D.card_le_of_part_subEquivalent hfin t s hts
  · exact D.card_le_rank_of_subEquivalent s
      (subEquivalent_of_le (D.part_mem s) (D.part_projection s) le_rfl)

lemma rank_one : D.rank 1=Fintype.card ι := by
  apply Nat.le_antisymm (D.rank_le_card 1)
  simpa only [Finset.card_univ] using D.card_le_rank_of_subEquivalent Finset.univ
    (subEquivalent_of_le (D.part_mem Finset.univ) (D.part_projection Finset.univ)
      (D.part_univ.le))

lemma rank_zero [Nontrivial H] (hfin : IsFiniteAlgebra M) : D.rank 0=0 := by
  simpa only [D.part_empty,Finset.card_empty] using D.rank_part hfin ∅

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
