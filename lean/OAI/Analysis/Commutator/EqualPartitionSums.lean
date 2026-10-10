import Mathlib
import OAI.Analysis.Commutator.EqualProjectionPartition
import OAI.Analysis.Commutator.ProjectionSumEquivalence
import OAI.Analysis.Commutator.DyadicPartition

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

local instance equalPartitionSumsDecidableEq : DecidableEq ι := Classical.decEq ι

def piece (i : ι) : H →L[ℂ] H := D.v i*star (D.v i)

def part (s : Finset ι) : H →L[ℂ] H := ∑ i∈s,D.piece i

lemma piece_mem (i : ι) : D.piece i∈M := M.mul_mem (D.mem i) (M.star_mem' (D.mem i))

lemma piece_projection (i : ι) : IsStarProjection (D.piece i) := D.final_projection i

lemma piece_cross (i j : ι) (hij : i≠j) : D.piece i*D.piece j=0 := D.final_cross i j hij

lemma part_mem (s : Finset ι) : D.part s∈M := M.sum_mem (fun i _ => D.piece_mem i)

lemma part_projection (s : Finset ι) : IsStarProjection (D.part s) :=
  orthogonal_sum_projection D.piece D.piece_projection D.piece_cross s

@[simp] lemma part_empty : D.part ∅=0 := by simp [part]

@[simp] lemma part_univ : D.part Finset.univ=1 := D.total

@[simp] lemma part_singleton (i : ι) : D.part {i}=D.piece i := by simp [part]

lemma part_insert (s : Finset ι) {i : ι} (hi : i∉s) : D.part (insert i s)=D.piece i+D.part s := by
  exact Finset.sum_insert hi

lemma part_mono {s t : Finset ι} (hst : s⊆t) : D.part s≤D.part t := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hst
  intro i _ _
  exact (D.piece_projection i).nonneg

lemma part_le_one (s : Finset ι) : D.part s≤1 := by
  simpa only [D.part_univ] using D.part_mono (Finset.subset_univ s)

lemma part_cross {s t : Finset ι} (hst : Disjoint s t) : D.part s*D.part t=0 := by
  rw [part,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  apply orthogonal_mul_sum_eq_zero D.piece D.piece_cross t
  exact fun ht => (Finset.disjoint_left.mp hst) hi ht

lemma base_equiv_piece (i : ι) : Equivalent M D.base (D.piece i) := by
  exact ⟨⟨D.v i,D.mem i,D.triple i,(D.initial i).le,le_rfl⟩,D.initial i,rfl⟩

lemma piece_equiv (i j : ι) : Equivalent M (D.piece i) (D.piece j) :=
  (D.base_equiv_piece i).symm.trans (D.piece_projection i) D.base_projection (D.base_equiv_piece j)

lemma part_equiv_of_card_eq (s t : Finset ι) (hst : s.card=t.card) :
    Equivalent M (D.part s) (D.part t) := by
  let f : s ≃ t := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hst)
  have h := Equivalent.finset_sum (M:=M) (fun i : s => D.piece i.val)
    (fun i : s => D.piece (f i).val)
    (fun i => D.piece_projection i.val) (fun i => D.piece_projection (f i).val)
    (fun i j hne => D.piece_cross i.val j.val (fun h => hne (Subtype.ext h)))
    (fun i j hne => D.piece_cross (f i).val (f j).val
      (fun h => hne (f.injective (Subtype.ext h))))
    (fun i => D.piece_equiv i.val (f i).val) Finset.univ
  have hf : (∑ i : s,D.piece (f i).val)=D.part t := by
    exact (f.sum_comp (fun j : t => D.piece j.val)).trans (Finset.sum_coe_sort t D.piece)
  simpa only [part,Finset.sum_coe_sort,hf] using h

lemma part_subEquivalent_of_card_le (s t : Finset ι) (hst : s.card≤t.card) :
    SubEquivalent M (D.part s) (D.part t) := by
  obtain ⟨r,hrt,hr⟩ := Finset.exists_subset_card_eq hst
  exact (D.part_equiv_of_card_eq s r hr.symm).subEquivalent.trans
    (D.part_projection s) (D.part_projection r)
    (subEquivalent_of_le (D.part_mem r) (D.part_projection r) (D.part_mono hrt))

lemma piece_ne_zero [Nontrivial H] (i : ι) : D.piece i≠0 := by
  intro hz
  have hv : D.v i=0 := by
    have ht := D.triple i
    change D.piece i*D.v i=D.v i at ht
    simpa only [hz,zero_mul] using ht.symm
  exact D.base_ne_zero (by rw [←D.initial i,hv,star_zero,zero_mul])

lemma part_ne_zero_of_nonempty [Nontrivial H] {s : Finset ι} (hs : s.Nonempty) : D.part s≠0 := by
  obtain ⟨i,hi⟩ := hs
  intro hz
  have hle : D.piece i≤D.part s := by
    simpa only [D.part_singleton] using D.part_mono (Finset.singleton_subset_iff.mpr hi)
  exact D.piece_ne_zero i (le_antisymm (hz ▸ hle) (D.piece_projection i).nonneg)

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
