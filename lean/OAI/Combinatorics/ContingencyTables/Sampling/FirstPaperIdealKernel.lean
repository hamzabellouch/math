import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperProposal
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperCompletionLaws

namespace OAI

/-! # Separate identification of the ideal small-state completion experiment -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open ResidualMixture FirstSuccess CompletionTranslation CompletionCounts FairBits

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
variable (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
variable (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "R" => referenceRows r c (d^20) (d^12) (stateCapacity r c) i₀
local notation "P" => referenceColumns r c (d^20) (d^12) (stateCapacity r c) j₀

/-- The ideal reference draw is transported from the nonempty physical
completion fibre, so no additional existence assumption is needed. -/
def idealReferenceLaw (z : PaperStates r c) : RationalLaw (Table (R z) (P z)) :=
  equivLaw (paperReferenceEquiv r c i₀ j₀ z) (uniformLaw (α := PaperFibre r c z))

lemma idealReferenceLaw_uniform (z : PaperStates r c) :
    let _ : Nonempty (Table (R z) (P z)) :=
      ⟨paperReferenceEquiv r c i₀ j₀ z (Classical.choice (inferInstance : Nonempty (PaperFibre r c z)))⟩
    idealReferenceLaw r c i₀ j₀ z=uniformLaw (α := Table (R z) (P z)) := by
  let : Nonempty (Table (R z) (P z)) :=
    ⟨paperReferenceEquiv r c i₀ j₀ z (Classical.choice (inferInstance : Nonempty (PaperFibre r c z)))⟩
  dsimp only
  exact uniform_equiv (paperReferenceEquiv r c i₀ j₀ z)

variable [Nonempty (PaperStates r c)]

theorem smallIdealStep_eq (x : PaperStates r c) :
    completionStepLaw R P (smallProposalLaw r c) (idealReferenceLaw r c i₀ j₀) x=
      smallTransitionLaw r c i₀ j₀ x := by
  let : ∀ z : PaperStates r c,Nonempty (Table (R z) (P z)) := fun z =>
    ⟨paperReferenceEquiv r c i₀ j₀ z (Classical.choice (inferInstance : Nonempty (PaperFibre r c z)))⟩
  have he : idealReferenceLaw r c i₀ j₀ =
      fun z => uniformLaw (α := Table (R z) (P z)) := by
    funext z
    exact idealReferenceLaw_uniform r c i₀ j₀ z
  rw [he]
  rw [completionStepLaw_proposal_at R P (smallProposalLaw r c)
    (fun _ => proposalLaw (proposalWeights r c x) (proposalWeights_nonnegative r c x)
      (proposalWeights_total r c x)) _ x rfl]
  apply uniformCompletionStep_eq R P
    (proposalWeights r c x) (proposalWeights_nonnegative r c x)
    (proposalWeights_total r c x) x (smallTransitionLaw r c i₀ j₀ x)
  intro y hy
  rw [smallTransitionLaw_mass_ne r c i₀ j₀ x y hy.symm]
  unfold smallMoveRat proposalWeights
  split_ifs <;> ring

end
end ContingencyTables.SmallGraphProfiles

end OAI
