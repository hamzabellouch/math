import OAI.GroupTheory.PolycyclicRecognition.Algebra.ApproximateMidpointProper
import Mathlib.Topology.Order.Compact

namespace OAI

/-! # Exact midpoints by compact minimization -/

namespace PolycyclicRecognition

open Set Metric

theorem exists_midpoint_of_proper {X : Type*} [MetricSpace X] [ProperSpace X]
    (hmid : HasApproximateMidpoints X) (x y : X) :
    ∃ z : X, dist x z ≤ dist x y / 2 ∧ dist z y ≤ dist x y / 2 := by
  let f : X → ℝ := fun z => max (dist x z) (dist z y)
  have hnonempty : (closedBall x (dist x y + 1)).Nonempty :=
    ⟨x, by simp only [mem_closedBall, dist_self]; positivity⟩
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall x (dist x y + 1)).exists_isMinOn
    hnonempty (show ContinuousOn f _ from
      ((continuous_const.dist continuous_id).max
        (continuous_id.dist continuous_const)).continuousOn)
  have hbound : f z ≤ dist x y / 2 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨w, h₁, h₂⟩ := hmid x y (min ε 1) (lt_min hε zero_lt_one)
    have hw : w ∈ closedBall x (dist x y + 1) := by
      rw [mem_closedBall, dist_comm w x]
      have := min_le_right ε (1 : ℝ)
      linarith [dist_nonneg (x := x) (y := y)]
    exact (hz hw).trans (max_le (h₁.trans (add_le_add_right (min_le_left ε 1) _))
      (h₂.trans (add_le_add_right (min_le_left ε 1) _)))
  exact ⟨z, (le_max_left _ _).trans hbound, (le_max_right _ _).trans hbound⟩

end PolycyclicRecognition

end OAI
