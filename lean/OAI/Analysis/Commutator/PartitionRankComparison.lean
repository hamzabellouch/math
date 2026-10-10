import Mathlib
import OAI.Analysis.Commutator.EqualPartitionSums

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

local instance : DecidableEq ι := Classical.decEq ι

lemma piece_mul_part_of_mem (s : Finset ι) {i : ι} (hi : i∈s) :
    D.piece i*D.part s=D.piece i := by
  rw [part,Finset.mul_sum,Finset.sum_eq_single_of_mem i hi]
  · exact (D.piece_projection i).isIdempotentElem.eq
  · intro j hj hne
    exact D.piece_cross i j hne.symm

lemma piece_mul_part_of_not_mem (s : Finset ι) {i : ι} (hi : i∉s) :
    D.piece i*D.part s=0 := orthogonal_mul_sum_eq_zero D.piece D.piece_cross s hi

lemma part_injective [Nontrivial H] : Function.Injective D.part := by
  intro s t hst
  apply Finset.ext
  intro i
  constructor
  · intro hi
    by_contra ht
    have h := D.piece_mul_part_of_mem s hi
    rw [hst,D.piece_mul_part_of_not_mem t ht] at h
    exact D.piece_ne_zero i h.symm
  · intro hi
    by_contra hs
    have h := D.piece_mul_part_of_mem t hi
    rw [←hst,D.piece_mul_part_of_not_mem s hs] at h
    exact D.piece_ne_zero i h.symm

lemma card_le_of_part_subEquivalent [Nontrivial H] (hfin : IsFiniteAlgebra M)
    (s t : Finset ι) (h : SubEquivalent M (D.part s) (D.part t)) : s.card≤t.card := by
  by_contra hle
  have hlt : t.card<s.card := Nat.lt_of_not_ge hle
  obtain ⟨r,hrs,hr⟩ := Finset.exists_subset_card_eq hlt.le
  have htr := (D.part_equiv_of_card_eq t r hr.symm).subEquivalent
  have hsr : SubEquivalent M (D.part s) (D.part r) :=
    h.trans (D.part_projection s) (D.part_projection t) htr
  have heq : D.part r=D.part s := finite_subEquivalent_antisymm_of_le hfin
    (D.part_mem s) (D.part_projection s) (D.part_mono hrs) hsr
  have hrc : r.card=s.card := congrArg Finset.card (D.part_injective heq)
  omega

lemma part_subEquivalent_iff_card_le [Nontrivial H] (hfin : IsFiniteAlgebra M)
    (s t : Finset ι) : SubEquivalent M (D.part s) (D.part t) ↔ s.card≤t.card :=
  ⟨D.card_le_of_part_subEquivalent hfin s t,D.part_subEquivalent_of_card_le s t⟩

lemma part_equivalent_iff_card_eq [Nontrivial H] (hfin : IsFiniteAlgebra M)
    (s t : Finset ι) : Equivalent M (D.part s) (D.part t) ↔ s.card=t.card := by
  constructor
  · intro h
    exact Nat.le_antisymm (D.card_le_of_part_subEquivalent hfin s t h.subEquivalent)
      (D.card_le_of_part_subEquivalent hfin t s h.symm.subEquivalent)
  · exact D.part_equiv_of_card_eq s t

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
