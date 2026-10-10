import OAI.MeasureTheory.Falconer.Recursion.BranchTransitions

namespace OAI

namespace PlanarFalconer

theorem BranchStep.width_decreases {A : ℕ → ℝ} {N q : ℕ} {sig : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hsig : 0 < sig)
    {s u : BranchState} {label : BranchLabel} (h : BranchStep A N q sig s label u)
    (hs : s.Valid N sig) (hu : u.Valid N sig) :
    u.finish-u.start < s.finish-s.start := by
  have hn := h.nested hq hs
  have hsd := BranchState.valid_depths hs
  have hud := BranchState.valid_depths hu
  have hstrict : s.start < u.start ∨ u.finish < s.finish := by
    cases h with
    | suffix hw _ =>
      have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hs.2 hw)
      exact Or.inr (by dsimp only [BranchState.finish]; omega)
    | low _ _ hg =>
      have hpos : 0 < sig*(N:ℝ) := mul_pos hsig (Nat.cast_pos.mpr hN)
      apply Or.inr
      apply (Nat.cast_lt (α := ℝ)).mp
      dsimp only [BranchState.finish]
      linarith
    | high hw _ _ _ =>
      have hp := policyDepth_interior A hq (policyBlocks_nonempty hq hs.2 hw)
      exact Or.inl (by dsimp only [BranchState.start]; omega)
    | near _ hp => exact Or.inl hp
    | far _ _ hm =>
      have hm := Finset.mem_Icc.mp hm
      exact Or.inl (by dsimp only [BranchState.start]; omega)
    | direct _ he => exact Or.inl he.anchor_gt
  omega

def branchPredecessor (A : ℕ → ℝ) (N q : ℕ) (sig : ℝ) (u s : BranchState) : Prop :=
  s.Valid N sig ∧ u.Valid N sig ∧ ∃ label, BranchStep A N q sig s label u

theorem branchPredecessor_wellFounded (A : ℕ → ℝ) {N q : ℕ} {sig : ℝ}
    (hN : 0 < N) (hq : 0 < q) (hsig : 0 < sig) :
    WellFounded (branchPredecessor A N q sig) := by
  apply Subrelation.wf (r := (measure (fun s : BranchState => s.finish-s.start)).rel) _
    (measure (fun s : BranchState => s.finish-s.start)).wf
  intro u s h
  obtain ⟨hs,hu,label,hstep⟩ := h
  exact hstep.width_decreases hN hq hsig hs hu

end PlanarFalconer

end OAI
