import OAI.MeasureTheory.Falconer.Recursion.BranchTransitions

namespace OAI

namespace PlanarFalconer

theorem high_depth_gap {N q t v : ℕ} {sig : ℝ} (hv : v ≤ t)
    (hgap : (t:ℝ)-v < sig*N) (hslack : sig*(N:ℝ) ≤ q) : t-v ≤ q := by
  have hcast : ((t-v:ℕ):ℝ) = (t:ℝ)-v := Nat.cast_sub hv
  exact Nat.cast_le.mp (by rw [hcast]; exact hgap.le.trans hslack)

theorem BranchStep.valid_successor {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    (hq : 0 < q) (hslack : sig*(N:ℝ) ≤ q)
    (hbuffer : ∀ L t a : ℕ, a < t-2*sourceFarBuffer N L sig →
      t-2*sourceFarBuffer N L sig+5 < t)
    {s u : BranchState} {label : BranchLabel}
    (h : BranchStep A N q sig s label u) (hv : s.Valid N sig) : u.Valid N sig := by
  cases h with
  | suffix hw _ =>
    have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    dsimp only [BranchState.Valid] at *
    omega
  | low _ hm _ =>
    have hm := Finset.mem_Ioc.mp hm
    dsimp only [BranchState.Valid] at *
    omega
  | high hw hs hm hg =>
    have hm := Finset.mem_Ioc.mp hm
    have hgap := high_depth_gap hm.2 hg hslack
    have hp := actual_prefix_policy_payment A hq hv.2 hw hs hm.2 hgap
    have hi := policyDepth_interior A hq (policyBlocks_nonempty hq hv.2 hw)
    exact ⟨by omega,by omega,hm.2,hv.2,by linarith⟩
  | near _ hs =>
    dsimp only [BranchState.Valid,BranchState.nearDepth,BranchState.finish,BranchState.descriptors] at *
    exact ⟨by omega,Nat.sub_le _ _,hv.2.2⟩
  | far _ hs hm =>
    have hb := hbuffer _ _ _ hs
    have hm := Finset.mem_Icc.mp hm
    dsimp only [BranchState.Valid,BranchState.nearDepth,BranchState.finish,BranchState.descriptors] at *
    exact ⟨by omega,by omega⟩
  | direct _ hw =>
    exact ⟨hv.1.trans hw.anchor_gt.le,hw.anchor_lt.le,hv.2.2⟩

theorem uniform_branch_successor_validity {sig kap : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hgap : sig < kap/1000) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      ∀ s u : BranchState, ∀ label : BranchLabel,
      s.Valid N sig → BranchStep A N (sourcePolicyBlock N kap) sig s label u →
      u.Valid N sig ∧ s.start ≤ u.start ∧ u.finish ≤ s.finish := by
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_source_ceiling_slack hsig hgap
  obtain ⟨N₂,h₂⟩ := uniform_source_far_buffer hsig
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN A s u label hv h
  have hq := sourcePolicyBlock_pos (by omega : 0 < N) hkap
  have hb : ∀ L t a : ℕ, a < t-2*sourceFarBuffer N L sig →
      t-2*sourceFarBuffer N L sig+5 < t := by
    intro L t a ha
    have hh := h₂ N (by omega) L t a ha
    omega
  exact ⟨h.valid_successor hq (h₁ N (by omega)).2.2 hb hv,h.nested hq hv⟩

end PlanarFalconer

end OAI
