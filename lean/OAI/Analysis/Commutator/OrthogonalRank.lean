import Mathlib
import OAI.Analysis.Commutator.EqualProjectionPartition
import OAI.Analysis.Commutator.EqualPartitionSums
import OAI.Analysis.Commutator.PartitionRank
import OAI.Analysis.Commutator.ProjectionComplements

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

local instance orthogonalRankDecidableEq : DecidableEq ι := Classical.decEq ι

lemma part_union {s t : Finset ι} (hst : Disjoint s t) : D.part (s∪t)=D.part s+D.part t :=
  Finset.sum_union hst

lemma part_compl (s : Finset ι) : D.part sᶜ=1-D.part s := by
  have h : D.part s+D.part sᶜ=1 := by
    have hh := Finset.sum_add_sum_compl s D.piece
    change D.part s+D.part sᶜ=D.part Finset.univ at hh
    rwa [D.part_univ] at hh
  exact eq_sub_of_add_eq' h

variable [Nontrivial H]

lemma rank_add_le_card (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hef : e*f=0) :
    D.rank e+D.rank f ≤ Fintype.card ι := by
  obtain ⟨s,hs,hse⟩ := D.exists_rank e he
  have hscomp := subEquivalent_complement M hfac hfin (D.part_mem s) heM
    (D.part_projection s) he hse
  have hfle : f ≤ 1-e := by
    apply le_sub_iff_add_le.mpr
    simpa only [add_comm f e] using (he.add hf hef).le_one
  have hfs : SubEquivalent M f (D.part sᶜ) := by
    rw [D.part_compl]
    exact (subEquivalent_of_le hfM hf hfle).trans hf he.one_sub hscomp
  have hr := D.rank_mono_subEquivalent hf hfs
  rw [D.rank_part hfin,Finset.card_compl] at hr
  have hsc := Finset.card_le_univ s
  omega

lemma orthogonal_rank_lower (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hef : e*f=0) :
    D.rank e+D.rank f ≤ D.rank (e+f) := by
  have hc := D.rank_add_le_card hfac hfin heM hfM he hf hef
  obtain ⟨s,hs,hse⟩ := D.exists_rank e he
  have hfc : D.rank f ≤ sᶜ.card := by rw [Finset.card_compl,hs]; omega
  obtain ⟨t,hts,ht⟩ := Finset.exists_subset_card_eq hfc
  have hst : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro i hi hit
    exact (Finset.mem_compl.mp (hts hit)) hi
  have htf := D.part_subEquivalent_of_card_le_rank hf t ht.le
  have hsub := hse.orthogonal_add (D.part_projection s) he (D.part_projection t) hf
    (D.part_cross hst) hef htf
  have hh : (s∪t).card ≤ D.rank (e+f) := D.card_le_rank_of_subEquivalent (s∪t)
    (by rwa [D.part_union hst])
  simpa only [Finset.card_union_of_disjoint hst,hs,ht] using hh

omit [Nontrivial H] in
lemma subEquivalent_part_of_rank_lt (hfac : FactorCorner.IsFactor M)
    {e : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e) (s : Finset ι)
    (hs : D.rank e<s.card) : SubEquivalent M e (D.part s) := by
  rcases factor_subEquivalent_total M hfac heM (D.part_mem s) he (D.part_projection s) with h|h
  · exact h
  · exact (Nat.not_le_of_lt hs (D.card_le_rank_of_subEquivalent s h)).elim

lemma orthogonal_rank_upper (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hef : e*f=0) :
    D.rank (e+f) ≤ D.rank e+D.rank f+2 := by
  by_cases hc : Fintype.card ι ≤ D.rank e+D.rank f+2
  · exact (D.rank_le_card (e+f)).trans hc
  have hsc : D.rank e+1 ≤ (Finset.univ : Finset ι).card := by rw [Finset.card_univ]; omega
  obtain ⟨s,hsu,hs⟩ := Finset.exists_subset_card_eq hsc
  have htc : D.rank f+1 ≤ sᶜ.card := by rw [Finset.card_compl,hs]; omega
  obtain ⟨t,hts,ht⟩ := Finset.exists_subset_card_eq htc
  have hst : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro i hi hit
    exact (Finset.mem_compl.mp (hts hit)) hi
  have hes := D.subEquivalent_part_of_rank_lt hfac heM he s (by omega)
  have hft := D.subEquivalent_part_of_rank_lt hfac hfM hf t (by omega)
  have hsub := hes.orthogonal_add he (D.part_projection s) hf (D.part_projection t)
    hef (D.part_cross hst) hft
  have hh : D.rank (e+f) ≤ D.rank (D.part (s∪t)) := D.rank_mono_subEquivalent (he.add hf hef)
    (by rwa [D.part_union hst])
  rw [D.rank_part hfin,Finset.card_union_of_disjoint hst,hs,ht] at hh
  omega

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
