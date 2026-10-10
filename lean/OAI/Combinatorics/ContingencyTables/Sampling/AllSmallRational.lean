import OAI.Combinatorics.ContingencyTables.Sampling.AllSmallChain
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperProposal
import OAI.Combinatorics.ContingencyTables.Transport.FiniteProposalStay
import OAI.Combinatorics.ContingencyTables.Transport.RationalChainMixing

namespace OAI

/-! # The actual rational walk on an empty large rectangle -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts CommonBasesFPRAS

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)
local instance : DecidableEq (PaperStates r c) := Classical.decEq _

def unitSmallStep (x : PaperStates r c) : RationalLaw (PaperStates r c) :=
  proposalStayLaw (proposalWeights r c x) (proposalWeights_nonnegative r c x)
    (proposalWeights_total r c x) x

lemma unitSmallStep_mass (x y : PaperStates r c) :
    (unitSmallStep r c x).mass y=proposalWeights r c x y+
      if x=y then 1-∑ z,proposalWeights r c x z else 0 :=
  proposalStayLaw_mass _ _ _ x y

variable [Nonempty (PaperStates r c)]

lemma unitSmallStep_cast (x y : PaperStates r c) :
    ((unitSmallStep r c x).mass y:ℝ)=(unitSmallChain r c).P x y := by
  rw [unitSmallStep_mass]
  simp only [Rat.cast_add,apply_ite,Rat.cast_sub,Rat.cast_one,Rat.cast_zero,Rat.cast_sum]
  simp only [proposalWeights,apply_ite,smallProposalRat_cast,Rat.cast_zero]
  simp only [unitSmallChain,MetropolisChain.chain,FiniteChain.ofMoves,MetropolisChain.move,
    div_self (one_ne_zero : (1:ℝ)≠0),min_self,mul_one]
  by_cases hxy : x=y <;> simp only [hxy,ite_true,ite_false]

lemma unitSmallChain_pi_lower
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (z : PaperStates r c) :
    1/(((stateBound r c+1:ℕ):ℝ)^(2*d)) ≤ (unitSmallChain r c).π z := by
  have hs : 0 < ∑ y,stateWeight r c y :=
    Finset.sum_pos (fun y _ => stateWeight_positive r c y) Finset.univ_nonempty
  rw [unitSmallChain_pi_weight r c hsmall]
  exact (one_div_le_one_div_of_le hs (state_total_mass_le r c)).trans
    (div_le_div_of_nonneg_right (stateWeight_ge_one r c z) hs.le)

theorem unitSmallWalk_variation [Nonempty I] [Nonempty J]
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (x : PaperStates r c) (n : ℕ) :
    (variation (walkLaw (unitSmallStep r c) x n)
      (uniformLaw (α := PaperStates r c)):ℝ) ≤
      ((stateBound r c+1:ℕ):ℝ)^(2*d)*Real.exp (-(n:ℝ)/(d:ℝ)^160) := by
  have hd : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by unfold dimensionAllowance; omega)
  have hm := (unitSmallChain r c).point_mixing_exp ((d:ℝ)^160)
    (1/(((stateBound r c+1:ℕ):ℝ)^(2*d))) (one_le_pow₀ hd) (by positivity)
    (unitSmallChain_pi_lower r c hsmall) (unitSmallChain_poincare r c hsmall) n x
  apply rationalWalk_variation (unitSmallStep r c) (unitSmallChain r c)
    (unitSmallStep_cast r c) (uniformLaw (α := PaperStates r c))
    (fun y => ?_) x n _ (by positivity)
  · simpa only [one_div,div_eq_mul_inv,one_mul,inv_inv,mul_comm] using hm
  · simp only [uniformLaw,uniformMass,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,
      unitSmallChain_pi]

end
end ContingencyTables.SmallGraphProfiles

end OAI
