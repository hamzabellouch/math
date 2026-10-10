import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperLocalNeighbors
import OAI.Combinatorics.ContingencyTables.Transport.ListBitProposal
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperBooleanProposal

namespace OAI

/-! # The small-chain proposal through the explicit local neighbor list -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open ResidualMixture FirstSuccess FairBits CompletionCounts

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "s" => smallProposalBits (I := I) (J := J)

lemma localNeighborList_codes (x : PaperStates r c) :
    (localNeighborList r c x).length ≤ 2^s := by
  calc
    _ ≤ 6*d^2 := localNeighborList_length r c x
    _ ≤ 32*d^2 := Nat.mul_le_mul_right _ (by decide)
    _ ≤ 2^s := Nat.le_pow_clog (by decide) _

/-- Binary lookup in the polynomial-length local list. -/
def localBitProposal (x : PaperStates r c) (bits : Fin s → Bool) : Option (PaperStates r c) :=
  listBitDraw (localNeighborList r c x) s bits

/-- The arithmetic enumeration implements exactly the proposal law used
in the accepted-chain and mixing proofs. -/
theorem localBitProposal_law (x : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin s → Bool)) (localBitProposal r c x)=
      smallProposalLaw r c x := by
  apply law_ext_except _ _ none
  intro y hy
  cases y with
  | none => exact False.elim (hy rfl)
  | some y =>
    have h := listBitDraw_mass_decidableEq (inferInstance : DecidableEq (Option (PaperStates r c)))
      (localNeighborList r c x)
      (localNeighborList_nodup r c x) s (localNeighborList_codes r c x) y
    change (mapLaw (uniformLaw (α := Fin s → Bool)) (localBitProposal r c x)).mass (some y)=_
      at h
    rw [h,smallProposalLaw_mass_some]
    unfold proposalWeights
    by_cases hxy : physicalAdjacent r c _ _ (stateCapacity r c) (stateCapacity_small r c) x y
    · have hy := (mem_localNeighborList r c x y).mpr hxy
      simp only [ite_eq_left hy,ite_eq_left hxy,smallProposalRat]
    · have hy := mt (mem_localNeighborList r c x y).mp hxy
      simp only [ite_eq_right hy,ite_eq_right hxy]

end
end ContingencyTables.SmallGraphProfiles

end OAI
