import OAI.Combinatorics.BalancedRyser.Construction.DeterministicReduction
import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletionFromSelection
import OAI.Combinatorics.BalancedRyser.Incidence.CorePencilAssembly
import OAI.Combinatorics.BalancedRyser.Probability.MainAssembly

namespace OAI

namespace Balanced
open scoped _root_.Balanced

theorem mainResult_of_candidate_selection_robustDeletion_primeStability_local
    (hcandidate : CandidateGraphResult.{0})
    (hselection : SelectionStatement.{0,0,0})
    (hdeletion : RobustDeletionResult.{0})
    (hstability : PrimeStability.{0})
    (hlocal : Local.PencilLocalResult.{0}) : MainResult :=
  mainResult_of_selectedDeletion_corePencil_local_deterministic
    deterministicReduction_proof
    (SelectedDeletion.result_of_candidate_and_selection hcandidate hselection)
    (corePencilResult_of_robustDeletion_primeStability hdeletion hstability)
    hlocal

end Balanced

end OAI
