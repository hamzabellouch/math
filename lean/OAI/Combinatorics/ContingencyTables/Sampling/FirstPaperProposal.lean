import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperSmallKernel
import OAI.Combinatorics.ContingencyTables.Transport.CompletionKernelIdentification

namespace OAI

/-! # The explicit small-state proposal realizes the proved ideal kernel -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

local notation "d" => dimensionAllowance (I := I) (J := J)

def proposalWeights (x y : PaperStates r c) : ℚ :=
  if physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c) x y
  then smallProposalRat d else 0

lemma proposalWeights_nonnegative (x y : PaperStates r c) : 0 ≤ proposalWeights r c x y := by
  unfold proposalWeights
  split_ifs
  · unfold smallProposalRat
    positivity
  · rfl

lemma smallProposalRat_cast (n : ℕ) : (smallProposalRat n:ℝ)=smallProposal n := by
  simp only [smallProposalRat,smallProposal,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]

lemma proposalWeights_total (x : PaperStates r c) : ∑ y,proposalWeights r c x y ≤ 1 := by
  let Adj := physicalAdjacent r c (d^20) (d^12) (stateCapacity r c) (stateCapacity_small r c) x
  have he : (∑ y,proposalWeights r c x y)=
      ((Finset.univ.filter Adj).card:ℚ)*smallProposalRat d := by
    change (∑ y,if Adj y then smallProposalRat d else 0)=_
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [he]
  have hb : ((5*d^2+1:ℕ):ℝ)*smallProposal d ≤ 1/2 :=
    smallProposal_degree d (by unfold dimensionAllowance; omega)
  have hd := physicalAdjacent_degree_allowance r c (d^20) (d^12)
    (stateCapacity r c) (stateCapacity_small r c) x
  have hp : 0 ≤ smallProposal d := (smallProposal_bounds d (by unfold dimensionAllowance; omega)).1.le
  have hh : ((Finset.univ.filter Adj).card:ℝ)*smallProposal d ≤ 1 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hd) hp).trans (hb.trans (by norm_num))
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_mul,Rat.cast_natCast,smallProposalRat_cast,Rat.cast_one] using hh

def smallProposalLaw (x : PaperStates r c) : RationalLaw (Option (PaperStates r c)) :=
  proposalLaw (proposalWeights r c x) (proposalWeights_nonnegative r c x) (proposalWeights_total r c x)

lemma smallProposalLaw_mass_some (x y : PaperStates r c) :
    (smallProposalLaw r c x).mass (some y)=proposalWeights r c x y := rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
