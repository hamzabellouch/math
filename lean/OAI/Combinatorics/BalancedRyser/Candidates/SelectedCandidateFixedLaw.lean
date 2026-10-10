import OAI.Combinatorics.BalancedRyser.Candidates.CandidateOccupancyBridge
import OAI.Combinatorics.BalancedRyser.Candidates.SelectionCandidateLaw
import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletionKernel

namespace OAI

namespace Balanced.SelectedDeletion

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [eqF : DecidableEq F]
local instance : DecidableEq (Slot F) := Classical.decEq _

def fixedLawOfSelection (M : MergedPairs F) {c C K ρ ε : ℝ}
    (hc : 0 < c) (hgood : CandidateGraphGood M c C) (hd : DistinctConstituents M)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (law : Selection.OutputLaw (candidateSelectionInput M J))
    (hsuccess : 1 - ε ≤ Selection.successMass law)
    (hcylinder : ∀ (S : Finset (Slot F)) (a : Slot F → AvailableCandidate M),
      Selection.cylinderMass law S a ≤ (K / (Fintype.card F : ℝ)) ^ S.card)
    (hoccupancy : Selection.occupancyFailureMass law (coordinatePlane F)
      (fun v : AvailableCandidate M => candidateLine v.val) (candidateTrackedSets M) ρ ≤ ε) :
    FixedLaw M K ρ ε := by
  cases Subsingleton.elim eqF (Classical.decEq F)
  exact {
  weight := law.labelWeight (fun _ v => v.val.2)
  nonnegative := Selection.labelWeight_nonneg law _
  mass_le_one := by
    convert Selection.sum_labelWeight_le_one law (fun _ v => v.val.2) using 1
    apply Finset.sum_congr
    · ext f; simp
    · intro f _; rfl
  supported := by
    intro f hf
    obtain ⟨a, ha, hpos⟩ := FinitePushforward.exists_positive_preimage
      (FinitePushforward.mapChoices (fun (_ : Slot F) (v : AvailableCandidate M) => v.val.2))
      law.weight law.nonnegative f hf
    have hs := candidateSelection_configuration_of_transversal M J a hd (law.supported a hpos)
    exact ha ▸ hs
  success_lower := by
    convert hsuccess using 1
    convert Selection.sum_labelWeight law (fun _ v => v.val.2) using 1
    apply Finset.sum_congr
    · ext f; simp
    · intro f _; rfl
  cylinder_le := by
    intro S f
    convert candidateSelection_label_cylinder M hc hgood J law hcylinder S f using 1
    apply Finset.sum_congr
    · ext t; simp
    · intro t _; split_ifs <;> rfl
  occupancy_le := by
    have hevent := candidateSelection_label_event M J law
      (fun f => ¬ (selectedConfiguration M f).Occupancy
        ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊)
    calc
      _ = ∑ a : Slot F → AvailableCandidate M,
          if ¬ (selectedConfiguration M (fun s => (a s).val.2)).Occupancy
            ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ then law.weight a else 0 := by
        convert hevent using 1
        all_goals
          apply Finset.sum_congr
          · ext t; simp
          · intro t _
            simp only [configuration, selectedConfiguration]
            exact (ite_eq_ite _ _ _).mpr trivial
      _ ≤ Selection.occupancyFailureMass law (coordinatePlane F)
          (fun v : AvailableCandidate M => candidateLine v.val) (candidateTrackedSets M) ρ :=
        by
          convert candidateSelection_occupancy_failure_mass_le hgood hd J law using 1
          apply Finset.sum_congr
          · ext a; simp
          · intro a _; split_ifs <;> rfl
      _ ≤ ε := hoccupancy

  }

end
end Balanced.SelectedDeletion

end OAI
