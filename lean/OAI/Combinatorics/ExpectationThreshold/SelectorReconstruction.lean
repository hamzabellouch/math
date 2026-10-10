import OAI.Combinatorics.ExpectationThreshold.SelectorDelayFeasibility

namespace OAI

/-!
# Minimal moves reconstruct inside the heavy sets

The family member in this theorem is any member witnessing feasibility of the
selected endpoint. It need not be the member restricting the changed set in
the minimization. This permits one witness to be used for an entire profile.
-/

noncomputable section

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every point moved into row `i` is heavy for every admissible cutoff of any
common feasibility witness. Otherwise its actual color can be delayed by one,
preserving that witness and contradicting minimal total movement. -/
theorem selected_movedRow_subset_heavySet {F : Family α} (mu : MassFamily F)
    {s : ℕ} (a z : Coloring α s) (hselected : Selected mu a z)
    (H : ↥F) (hfeasible : FeasibleFor mu a z H) (i : Fin s) (ε : ℝ)
    (hε : Admissible (mu.weight H) (prefixSet z i)
      (crossings a z i : ℝ) (dscale i) ε) :
    movedRow a z i ⊆ heavySet (mu.weight H) ε := by
  classical
  intro x hxrow
  obtain ⟨hx, hmove⟩ := (Finset.mem_filter.mp hxrow).2
  apply mem_heavySet.mpr
  by_contra hheavy
  have hweight : mu.weight H x ≤ ε := le_of_not_gt hheavy
  obtain ⟨H₀, hbounded, hminimal⟩ := hselected
  have hbounded' : BoundedFeasible mu a H₀ (delayColor z x i) := by
    refine ⟨⟨earlier_delayColor a z x i hx hmove hbounded.1.1, ?_⟩, ?_⟩
    · exact ⟨H, feasibleFor_delayColor mu a z H hfeasible x i hx hmove ε hε hweight⟩
    · intro y hy
      exact hbounded.2 (changes_delayColor_subset a z x i hx hy)
  have hmin := hminimal (delayColor z x i) hbounded'
  have hdec := movement_delayColor_add_one a z x i hx hmove
  have hstrict : movement a (delayColor z x i) < movement a z :=
    lt_of_lt_of_eq (Nat.lt_succ_self _) hdec
  exact (not_lt_of_ge hmin) hstrict

/-- The same reconstruction statement with the heavy set written explicitly. -/
theorem selected_movedRow_subset_filter {F : Family α} (mu : MassFamily F)
    {s : ℕ} (a z : Coloring α s) (hselected : Selected mu a z)
    (H : ↥F) (hfeasible : FeasibleFor mu a z H) (i : Fin s) (ε : ℝ)
    (hε : Admissible (mu.weight H) (prefixSet z i)
      (crossings a z i : ℝ) (dscale i) ε) :
    movedRow a z i ⊆ Finset.univ.filter (fun x => ε < mu.weight H x) := by
  simpa only [heavySet] using
    selected_movedRow_subset_heavySet mu a z hselected H hfeasible i ε hε

end TalagrandThreshold.Selector

end

end OAI
