import Mathlib
import OAI.Analysis.Commutator.DyadicPartition
import OAI.Analysis.Commutator.EqualPartitionSums
import OAI.Analysis.Commutator.PartitionRank

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

variable (w : Link M D.base D.base) (hww : w.val*w.val=0) (hsum : w.initial+w.final=D.base)

lemma double_piece_sum (i : ι) :
    (∑ b : Bool,(D.double w hww hsum).piece (i,b))=D.piece i := by
  rw [Fintype.sum_bool]
  simp only [piece,double_val,Bool.false_eq_true,↓reduceIte,star_mul,
    w.initial_projection.isSelfAdjoint.star_eq]
  have hi : w.initial*w.initial=w.initial := w.initial_projection.isIdempotentElem.eq
  calc
    _=D.v i*(w.final+w.initial*w.initial)*star (D.v i) := by
      dsimp only [Link.final]
      noncomm_ring
    _=D.v i*D.base*star (D.v i) := by rw [hi,add_comm w.final,hsum]
    _=D.piece i := by rw [D.source]; rfl

lemma double_part (s : Finset ι) :
    (D.double w hww hsum).part ((s ×ˢ Finset.univ))=D.part s := by
  change (∑ j∈(s ×ˢ Finset.univ),(D.double w hww hsum).piece j)=_
  rw [Finset.sum_product]
  simp only [double_piece_sum]
  rfl

lemma double_rank_lower {e : H →L[ℂ] H} (he : IsStarProjection e) :
    2*D.rank e≤(D.double w hww hsum).rank e := by
  obtain ⟨s,hs,hse⟩ := D.exists_rank e he
  have h := (D.double w hww hsum).card_le_rank_of_subEquivalent ((s ×ˢ Finset.univ))
    (by rwa [D.double_part w hww hsum])
  simpa only [Finset.card_product,Finset.card_univ,Fintype.card_bool,hs,Nat.mul_comm] using h

lemma double_rank_upper {e : H →L[ℂ] H} (he : IsStarProjection e) :
    (D.double w hww hsum).rank e≤2*D.rank e+1 := by
  by_cases hk : D.rank e=Fintype.card ι
  · have h := (D.double w hww hsum).rank_le_card e
    rw [Fintype.card_prod,Fintype.card_bool] at h
    omega
  have hklt : D.rank e<Fintype.card ι := lt_of_le_of_ne (D.rank_le_card e) hk
  obtain ⟨s,hsu,hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (by
    simpa only [Finset.card_univ] using Nat.succ_le_of_lt hklt)
  by_contra hnot
  have hnew : (s ×ˢ (Finset.univ : Finset Bool)).card≤(D.double w hww hsum).rank e := by
    rw [Finset.card_product,Finset.card_univ,Fintype.card_bool,hs]
    omega
  have hse : SubEquivalent M (D.part s) e := by
    have h := (D.double w hww hsum).part_subEquivalent_of_card_le_rank he
      ((s ×ˢ Finset.univ)) hnew
    rwa [D.double_part w hww hsum] at h
  have h := D.card_le_rank_of_subEquivalent s hse
  omega

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
