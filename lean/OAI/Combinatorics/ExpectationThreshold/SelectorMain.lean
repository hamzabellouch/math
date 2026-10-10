import OAI.Combinatorics.ExpectationThreshold.SelectorFeasibility
import OAI.Combinatorics.ExpectationThreshold.SelectorGlobalCost
import OAI.Combinatorics.ExpectationThreshold.SelectorAverageColor
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# The simultaneous multiscale selector

The actual minimum-move cover bounds the bad probability from below by its
weighted cost. The profile reconstruction and counting theorem bounds that
same cost from above. Both conclusions use the literal independent color law.
-/

noncomputable section
open scoped BigOperators Classical

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The actual selected changed sets give the cover-cost inequality. -/
theorem half_bad_probability_le_selected_cost {F : Family α}
    (mu : MassFamily F) (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (hF : ¬ Small p F) :
    (1 / 2 : ℝ) * (coloringLaw (α := α) p s hp hs).prob (Bad mu) ≤
      ∑ a : Coloring α s, if Bad mu a then
        colorMass p s a * ∑ z ∈ selectedMoves mu a, p ^ (changes a z).card
      else 0 := by
  classical
  unfold FiniteLaw.prob
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : Bad mu a
  · simp only [ite_eq_left ha, coloringLaw_weight]
    have hcover := (half_lt_selectedMoves_cost mu a hp.le hF).le
    have hmass := colorMass_nonneg p s hp hs a
    nlinarith
  · simp only [ite_eq_right ha, mul_zero, le_refl]

/-- The actual bad event has probability at most one tenth. -/
theorem bad_probability_le_one_tenth {F : Family α}
    (mu : MassFamily F) (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (hF : ¬ Small p F) :
    (coloringLaw (α := α) p s hp hs).prob (Bad mu) ≤ 1 / 10 := by
  have hcover := half_bad_probability_le_selected_cost mu p s hp hs hF
  have hcount := weighted_bad_selected_cost_le mu p s hp hs
  linarith

/-- One family member is simultaneously captured at every scale. -/
theorem simultaneous_capture (F : Family α) (_hF : F.Nonempty)
    (_hsets : ∀ H ∈ F, H.Nonempty) (mu : MassFamily F)
    (p : ℝ) (hp0 : 0 < p) (_hp1 : p ≤ 1) (hnotsmall : ¬ Small p F)
    (s : ℕ) (hs : p * scaleSum s ≤ 1 / 2) :
    (9 / 10 : ℝ) ≤
      (coloringLaw (α := α) p s hp0 hs).prob (Captured mu) := by
  have hbad := bad_probability_le_one_tenth mu p s hp0 hs hnotsmall
  have hcompl := (coloringLaw (α := α) p s hp0 hs).prob_compl (Captured mu)
  change (coloringLaw (α := α) p s hp0 hs).prob (fun a => ¬ Captured mu a) ≤
    1 / 10 at hbad
  linarith

/-- With probability at least nine tenths, one member has mean color at most two. -/
theorem average_color (F : Family α) (hF : F.Nonempty)
    (hsets : ∀ H ∈ F, H.Nonempty) (mu : MassFamily F)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hnotsmall : ¬ Small p F)
    (s : ℕ) (hs : p * scaleSum s ≤ 1 / 2) :
    (9 / 10 : ℝ) ≤ (coloringLaw (α := α) p s hp0 hs).prob
      (fun a => ∃ H : ↥F, meanColor mu H a ≤ 2) := by
  exact (simultaneous_capture F hF hsets mu p hp0 hp1 hnotsmall s hs).trans
    ((coloringLaw (α := α) p s hp0 hs).prob_mono
      fun _ ha => ha.exists_meanColor_le_two)

end TalagrandThreshold.Selector

end

end OAI
