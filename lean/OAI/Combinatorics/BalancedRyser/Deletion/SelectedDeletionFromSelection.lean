import OAI.Combinatorics.BalancedRyser.Candidates.SelectedCandidateFixedLaw
import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletionAssembly

namespace OAI

noncomputable section

namespace Balanced.SelectedDeletion

universe u

theorem uniform_fixedLaws_of_selection (hselection : SelectionStatement.{u,u,u})
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ K ρ : ℝ, ∃ ε : ℕ → ℝ, ∃ N : ℕ,
      0 < K ∧ 0 < ρ ∧ (∀ q, 0 ≤ ε q) ∧
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F → ∀ M : MergedPairs F,
          InitialGood M c C → Nonempty (FixedLaw M K ρ (ε (Fintype.card F))) := by
  classical
  obtain ⟨K, ρ, ε, N, hK, hρ, hε, hlim, hselect⟩ :=
    hselection c C (1 / 5) hc hC (by norm_num) (by norm_num)
  refine ⟨K, ρ, ε, N, hK, hρ, hε, hlim, ?_⟩
  intro F _ _ _ hlarge M hM
  obtain ⟨J, hJ⟩ := candidateGraphGood_selection hM.1
  obtain ⟨law, hsuccess, hcylinder, hoccupancy⟩ :=
    hselect (Fintype.card F) hlarge (Slot F) (AvailableCandidate M)
      (candidateSelectionInput M J) hJ
  have hocc := hoccupancy (Point F) (Direction F) (Line F) (coordinatePlane F)
    (Equiv.refl (Slot F)) (fun v : AvailableCandidate M => candidateLine v.val)
    (candidateSelection_lineAssignment M J) (candidateTrackedSets M)
    (candidateSelection_trackedSets hM.1)
  exact ⟨fixedLawOfSelection M hc hM.1 hM.2 J law hsuccess hcylinder hocc⟩

theorem result_of_candidate_and_selection
    (hcandidate : CandidateGraphResult.{u})
    (hselection : SelectionStatement.{u,u,u}) : SelectedDeletionResult.{u} :=
  result_of_uniform_fixedLaws hcandidate (uniform_fixedLaws_of_selection hselection)

end Balanced.SelectedDeletion

end

end OAI
