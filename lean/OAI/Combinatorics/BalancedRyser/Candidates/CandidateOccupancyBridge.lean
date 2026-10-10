import OAI.Combinatorics.BalancedRyser.Candidates.CandidateSelectionBridge
import OAI.Combinatorics.BalancedRyser.Incidence.SelectionAffineAdapter

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def candidateTrackedSets (M : MergedPairs F) : Line F → Finset (Point F) :=
  SelectionOccupancy.initial (selectedConfiguration M (fun _ => 0))

theorem candidateTrackedSets_eq (M : MergedPairs F) (f : Slot F → F) :
    candidateTrackedSets M = SelectionOccupancy.initial (selectedConfiguration M f) := rfl

theorem candidateSelection_trackedSets {M : MergedPairs F} {c C : ℝ}
    (hgood : CandidateGraphGood M c C) :
    Selection.TrackedSets (coordinatePlane F) (candidateTrackedSets M) (1 / 5) := by
  exact SelectionOccupancy.candidate_good_trackedSets
    (selectedConfiguration M (fun _ => 0)) hgood

theorem candidateSelection_output_line (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (a : Slot F → AvailableCandidate M)
    (ha : Selection.IsIndependentTransversal (candidateSelectionInput M J) a)
    (s : Slot F) :
    candidateLine (a s).val =
      ((selectedConfiguration M (fun t => (a t).val.2)).choice s).line := by
  change ((a s).val.1.1, (a s).val.2) = (s.1, (a s).val.2)
  have hs : (a s).val.1 = s := ha.1 s
  rw [hs]

theorem candidateSelection_finalTracked (M : MergedPairs F)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (a : Slot F → AvailableCandidate M)
    (ha : Selection.IsIndependentTransversal (candidateSelectionInput M J) a)
    (l : Line F) :
    Selection.finalTracked (coordinatePlane F) (fun v : AvailableCandidate M =>
      candidateLine v.val) (candidateTrackedSets M) a l =
      SelectionOccupancy.final (selectedConfiguration M (fun s => (a s).val.2)) l := by
  rw [candidateTrackedSets_eq M (fun s => (a s).val.2)]
  exact SelectionOccupancy.selection_finalTracked_eq _ _ a
    (candidateSelection_output_line M J a ha) l

theorem candidateSelection_occupancy_of_no_failure {M : MergedPairs F} {c C ρ : ℝ}
    (hgood : CandidateGraphGood M c C) (hd : DistinctConstituents M)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (a : Slot F → AvailableCandidate M)
    (ha : Selection.IsIndependentTransversal (candidateSelectionInput M J) a)
    (hoccup : ∀ l : Line F, ρ * Fintype.card F ≤
      ((Selection.finalTracked (coordinatePlane F)
        (fun v : AvailableCandidate M => candidateLine v.val)
        (candidateTrackedSets M) a l).card : ℝ)) :
    (selectedConfiguration M (fun s => (a s).val.2)).Occupancy
      ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ := by
  have hv := (candidateSelection_configuration_of_transversal M J a hd ha).1
  apply SelectionOccupancy.occupancy_of_candidate_good_final _ hv hgood
  intro l
  simpa only [candidateSelection_finalTracked M J a ha l] using hoccup l

theorem candidateSelection_occupancy_failure_mass_le {M : MergedPairs F} {c C ρ : ℝ}
    (hgood : CandidateGraphGood M c C) (hd : DistinctConstituents M)
    (J : AvailableCandidate M → Finset (CandidateVertex F))
    (law : Selection.OutputLaw (candidateSelectionInput M J)) :
    (∑ a : Slot F → AvailableCandidate M,
      if ¬ (selectedConfiguration M (fun s => (a s).val.2)).Occupancy
      ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ then law.weight a else 0) ≤
    Selection.occupancyFailureMass law (coordinatePlane F)
      (fun v : AvailableCandidate M => candidateLine v.val) (candidateTrackedSets M) ρ := by
  rw [Selection.occupancyFailureMass, Finset.sum_filter]
  classical
  have huniv : @Finset.univ (Slot F → AvailableCandidate M)
      (@Pi.instFintype (Slot F) (fun _ => AvailableCandidate M)
        (fun a b => Classical.propDecidable (a = b)) inferInstance (fun _ => inferInstance)) =
      (Finset.univ : Finset (Slot F → AvailableCandidate M)) := by
    ext a
    simp
  rw [huniv]
  apply Finset.sum_le_sum
  intro a _
  by_cases hb : ¬ (selectedConfiguration M (fun s => (a s).val.2)).Occupancy
      ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊
  · rw [ite_eq_left hb]
    by_cases hw : 0 < law.weight a
    · have ha := law.supported a hw
      have hf : ∃ l : Line F,
          ((Selection.finalTracked (coordinatePlane F)
            (fun v : AvailableCandidate M => candidateLine v.val)
            (candidateTrackedSets M) a l).card : ℝ) < ρ * Fintype.card F := by
        by_contra h
        apply hb
        apply candidateSelection_occupancy_of_no_failure hgood hd J a ha
        intro l
        exact le_of_not_gt (fun hl => h ⟨l, hl⟩)
      rw [ite_eq_left hf]
    · have hz : law.weight a = 0 :=
        le_antisymm (le_of_not_gt hw) (law.nonnegative a)
      simp only [hz, ite_self, le_refl]
  · rw [ite_eq_right hb]
    split_ifs
    · exact law.nonnegative a
    · exact le_refl 0

end
end Balanced

end OAI
