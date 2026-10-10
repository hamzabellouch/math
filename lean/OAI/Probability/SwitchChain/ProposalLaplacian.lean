import OAI.Probability.SwitchChain.SwitchLaplacian
import OAI.Probability.SwitchChain.SwitchMultiplicity

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Problem315

theorem switchLaplacian_eq_sum_proposals {n : Nat} {d : Fin n → Nat}
    (f : GraphState n d → ℝ) (G : GraphState n d) :
    switchLaplacian n d f G =
      ∑ p ∈ allProposals n, (f G - f (proposalState G p)) := by
  have hterm (H : GraphState n d) :
      (if SwitchStep n d G H then f G - f H else 0) =
        (((allProposals n).filter (fun p => proposalResult G.val p = H.val)).card : ℝ) *
          (f G - f H) := by
    by_cases hGH : G = H
    · subst H
      simp
    · have hv : G.val ≠ H.val := fun h => hGH (Subtype.ext h)
      by_cases hs : SwitchStep n d G H
      · obtain ⟨p, hvalid, hp⟩ := hs
        rw [ite_eq_left ⟨p, hvalid, hp⟩, proposal_count_eq_one hv ⟨p, hp⟩]
        simp
      · rw [ite_eq_right hs, proposal_count_eq_zero]
        · simp
        · rintro ⟨p, hp⟩
          apply hs
          refine ⟨p, ?_, hp⟩
          apply validSwitch_of_proposalResult_ne
          rw [hp]
          exact Ne.symm hv
  unfold switchLaplacian
  simp_rw [hterm]
  calc
    _ = ∑ H ∈ allGraphStates n d, ∑ p ∈ allProposals n,
        if proposalState G p = H then f G - f H else 0 := by
      apply Finset.sum_congr rfl
      intro H hH
      rw [← Finset.sum_filter]
      have hfilter : (allProposals n).filter (fun p => proposalState G p = H) =
          (allProposals n).filter (fun p => proposalResult G.val p = H.val) := by
        ext p
        simp only [Finset.mem_filter, and_congr_right_iff]
        intro _
        exact Subtype.ext_iff
      rw [hfilter]
      simp
      ring
    _ = ∑ p ∈ allProposals n, (f G - f (proposalState G p)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      simp [allGraphStates]

theorem sum_pairProposalLaplacian_eq {n : Nat} {d : Fin n → Nat}
    {ι : Type*} (pairs : Finset ι) (crosses : ι → SwitchProposal n → Prop)
    [∀ a p, Decidable (crosses a p)]
    (hcount : ∀ p : SwitchProposal n, (pairs.filter (fun a => crosses a p)).card = 2)
    (f : GraphState n d → ℝ) (G : GraphState n d) :
    (∑ a ∈ pairs, ∑ p ∈ allProposals n,
      if crosses a p then f G - f (proposalState G p) else 0) =
      2 * switchLaplacian n d f G := by
  rw [Finset.sum_comm, switchLaplacian_eq_sum_proposals, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_filter]
  simp [hcount p]
  ring

theorem sum_pairProposalLaplacian_eq_of_valid {n : Nat} {d : Fin n → Nat}
    {ι : Type*} (pairs : Finset ι) (crosses : ι → SwitchProposal n → Prop)
    [∀ a p, Decidable (crosses a p)]
    (f : GraphState n d → ℝ) (G : GraphState n d)
    (hcount : ∀ p : SwitchProposal n, validSwitch G.val p →
      (pairs.filter (fun a => crosses a p)).card = 2) :
    (∑ a ∈ pairs, ∑ p ∈ allProposals n,
      if crosses a p then f G - f (proposalState G p) else 0) =
      2 * switchLaplacian n d f G := by
  rw [Finset.sum_comm, switchLaplacian_eq_sum_proposals, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hv : validSwitch G.val p
  · rw [← Finset.sum_filter]
    simp [hcount p hv]
    ring
  · have heq : proposalState G p = G := by
      apply Subtype.ext
      simp [proposalState, proposalResult, hv]
    simp [heq]

def pairSwitchLaplacian (n : Nat) (d : Fin n → Nat) (a : Finset (Fin n))
    (f : GraphState n d → ℝ) (G : GraphState n d) : ℝ :=
  ∑ p ∈ allProposals n,
    if a ∈ SwitchPairFiber.crossingPairs p then f G - f (proposalState G p) else 0

theorem sum_pairSwitchLaplacian {n : Nat} {d : Fin n → Nat}
    (f : GraphState n d → ℝ) (G : GraphState n d) :
    (∑ a ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
      pairSwitchLaplacian n d a f G) = 2 * switchLaplacian n d f G := by
  unfold pairSwitchLaplacian
  refine sum_pairProposalLaplacian_eq_of_valid
    ((Finset.univ : Finset (Fin n)).powersetCard 2)
    (fun a p => a ∈ SwitchPairFiber.crossingPairs p) f G ?_
  intro p hp
  have heq : ((Finset.univ : Finset (Fin n)).powersetCard 2).filter
      (fun a => a ∈ SwitchPairFiber.crossingPairs p) = SwitchPairFiber.crossingPairs p := by
    ext a
    constructor
    · intro ha
      exact (Finset.mem_filter.mp ha).2
    · intro ha
      refine Finset.mem_filter.mpr ⟨?_, ha⟩
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.subset_univ a, ?_⟩
      exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp ha).1).2
  rw [heq]
  exact SwitchPairFiber.crossingPairs_card p hp

end Problem315

end

end OAI
