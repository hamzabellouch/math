import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperProposal
import OAI.Combinatorics.ContingencyTables.Transport.FiniteLawDecidableEq

namespace OAI

/-! # Finite Boolean realization of the small graph proposal law -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts FairBits

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

local notation "d" => dimensionAllowance (I := I) (J := J)

abbrev smallProposalBits : ℕ := Nat.clog 2 (32*d^2)

lemma smallProposal_codes (x : PaperStates r c) :
    Fintype.card {y // physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c) x y} ≤
      2^(smallProposalBits (I := I) (J := J)) := by
  rw [Fintype.card_subtype]
  apply (physicalAdjacent_degree_allowance r c _ _ (stateCapacity r c)
    (stateCapacity_small r c) x).trans
  have hd : 1 ≤ d := by unfold dimensionAllowance; omega
  have hs : 1 ≤ d^2 := one_le_pow₀ hd
  exact (show 5*d^2+1 ≤ 32*d^2 by omega).trans (Nat.le_pow_clog (by decide) _)

def smallBitProposal (x : PaperStates r c)
    (bits : Fin (smallProposalBits (I := I) (J := J)) → Bool) : Option (PaperStates r c) :=
  subsetBitDraw (physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c) x)
    (smallProposalBits (I := I) (J := J)) (smallProposal_codes r c x) bits

/-- The law is independent of the equality decision used by a consumer. -/
theorem smallBitProposal_law_decidableEq (d₀ : DecidableEq (Option (PaperStates r c)))
    (x : PaperStates r c) :
    @mapLaw (Fin (smallProposalBits (I := I) (J := J)) → Bool)
      (Option (PaperStates r c)) _ _ d₀
      (uniformLaw (α := Fin (smallProposalBits (I := I) (J := J)) → Bool))
      (smallBitProposal r c x)=smallProposalLaw r c x := by
  apply law_ext_except _ _ none
  intro y hy
  cases y with
  | none => exact False.elim (hy rfl)
  | some y =>
    exact (subsetBitDraw_mass_decidableEq d₀
      (physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c) x)
      (smallProposalBits (I := I) (J := J)) (smallProposal_codes r c x) y).trans
        (smallProposalLaw_mass_some r c x y).symm

/-- The coding assigns one bit word to each distinct neighbor and uses
all remaining words for the holding proposal. Enumeration cost is separate. -/
theorem smallBitProposal_law (x : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin (smallProposalBits (I := I) (J := J)) → Bool))
      (smallBitProposal r c x)=smallProposalLaw r c x :=
  smallBitProposal_law_decidableEq r c _ x


end
end ContingencyTables.SmallGraphProfiles

end OAI
