import OAI.Probability.SwitchChain.MatchingCount
import OAI.Probability.SwitchChain.SwitchFoundations

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315

def proposalState {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (p : SwitchProposal n) : GraphState n d :=
  ⟨proposalResult G.val p, proposalResult_realizes G.property p⟩

theorem proposal_fiber_cards_sum {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) :
    (∑ H ∈ allGraphStates n d,
      ((allProposals n).filter (fun p => proposalResult G.val p = H.val)).card) =
      (allProposals n).card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (allProposals n) (allGraphStates n d) (proposalState G)
  have hf (H : GraphState n d) :
      ((allProposals n).filter (fun p => proposalState G p = H)) =
      ((allProposals n).filter (fun p => proposalResult G.val p = H.val)) := by
    ext p
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro _
    exact Subtype.ext_iff
  simp_rw [hf] at h
  simpa only [allGraphStates, Finset.mem_univ, Finset.filter_true] using h

theorem switchKernel_row_sum {n : ℕ} {d : Fin n → ℕ}
    (hn : 4 ≤ n) (G : GraphState n d) :
    (∑ H ∈ allGraphStates n d, switchKernel n d G H) = 1 := by
  classical
  have hc : (Nat.choose n 4 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hn))
  unfold switchKernel
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Nat.cast_sum,
    proposal_fiber_cards_sum, MatchingCount.allProposals_card]
  have hdiag : (∑ H ∈ allGraphStates n d, if G = H then (1 : ℝ) / 2 else 0) = 1 / 2 := by
    simp [allGraphStates]
  rw [hdiag]
  push_cast
  field_simp
  ring

theorem switchKernel_column_sum {n : ℕ} {d : Fin n → ℕ}
    (hn : 4 ≤ n) (H : GraphState n d) :
    (∑ G ∈ allGraphStates n d, switchKernel n d G H) = 1 := by
  simp_rw [switchKernel_symm (_ : GraphState n d) H]
  exact switchKernel_row_sum hn H

end Problem315

end

end OAI
