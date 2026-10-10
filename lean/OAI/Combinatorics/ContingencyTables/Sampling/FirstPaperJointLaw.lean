import OAI.Combinatorics.ContingencyTables.Transport.CompletionFibreEquiv
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperRationalMixing
import OAI.Combinatorics.ContingencyTables.Transport.FiniteDependentLaw

namespace OAI

/-! # Uniformity of the actual state/completion joint law -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open ResidualMixture FirstSuccess CompletionTranslation SmallContextFibres

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev PaperFibre (r : I → ℕ) (c : J → ℕ) (z : PaperStates r c) :=
  CompletionFibre (paperSmall r c) (stateCapacity r c) r
    (fun i => r i+rowLargeCount (paperSmall r c) i*((dimensionAllowance (I := I) (J := J))^12)) c
    (fun j => c j+columnLargeCount (paperSmall r c) j*((dimensionAllowance (I := I) (J := J))^12))
    (physicalProfile _ (stateCapacity r c) r c _ z)

noncomputable instance paperFibreNonempty (r : I → ℕ) (c : J → ℕ) (z : PaperStates r c) :
    Nonempty (PaperFibre r c z) := by
  apply Fintype.card_pos_iff.mp
  have hp := stateWeight_positive r c z
  change 0 < hardMarginal _ _ _ _ _ _ at hp
  rw [hardMarginal_eq_fibre_card (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12)
    (physicalProfile _ (stateCapacity r c) r c _ z) (naturalProfile_bounded z.val.val)] at hp
  exact_mod_cast hp

abbrev PaperStateJoint (r : I → ℕ) (c : J → ℕ) := (z : PaperStates r c) × PaperFibre r c z

lemma paperFibre_card_block (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (z : PaperStates r c) :
    Fintype.card (PaperFibre r c z)=
      blockCount (referenceRows r c _ _ (stateCapacity r c) i₀)
        (referenceColumns r c _ _ (stateCapacity r c) j₀) z :=
  Fintype.card_congr (referenceFibreEquiv r c _ _ (stateCapacity r c) i₀ j₀ z
    (physical_paper_capacity _ r c _ _ _ dimension_le_allowance z))

noncomputable def stationaryJointLaw (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20)) :
    RationalLaw (PaperStateJoint r c) :=
  dependentJointLaw (smallStationaryLaw r c i₀ j₀) (fun z => uniformLaw (α := PaperFibre r c z))

/-- The law keeps the completion multiplicity exactly: each full pair
has the same probability, including pairs above defective small states. -/
theorem stationaryJointLaw_uniform (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20)) :
    stationaryJointLaw r c i₀ j₀=uniformLaw (α := PaperStateJoint r c) := by
  apply dependentJointLaw_uniform
  intro z
  simp only [paperFibre_card_block r c i₀ j₀]
  rfl

/-- Cardinality of the full joint space is the small chain normalizer. -/
theorem paperStateJoint_card (r : I → ℕ) (c : J → ℕ) :
    (Fintype.card (PaperStateJoint r c):ℝ)=∑ z,stateWeight r c z := by
  rw [Fintype.card_sigma,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact (hardMarginal_eq_fibre_card (paperSmall r c) (stateCapacity r c) r c
    ((dimensionAllowance (I := I) (J := J))^12)
    (physicalProfile _ (stateCapacity r c) r c _ z) (naturalProfile_bounded z.val.val)).symm

end ContingencyTables.SmallGraphProfiles

end OAI
