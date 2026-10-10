import Mathlib
import OAI.MathematicalPhysics.PrefixFlows.Effective

namespace OAI

/-! Separation of the initial loading pulse from the repeated template. -/

noncomputable section
open scoped ContDiff
namespace PrefixFlows
@[simp] theorem point_time (t : ℝ) (x : Space) : point t x 0 = t := rfl

@[simp] theorem position_point (t : ℝ) (x : Space) : position (point t x) = x := by
  ext i
  fin_cases i <;> rfl

theorem assemble_during_loading (template : Machine → Field)
    (loading : Machine → List ℕ → Field) (M : Machine) (w : List ℕ)
    (t : ℝ) (x : Space) (ht : t < 1) :
    assemble template loading M w (point t x) = loading M w (point t x) := by
  simp only [assemble, point_time]
  exact ite_eq_left ht

theorem assemble_after_loading (template : Machine → Field)
    (loading : Machine → List ℕ → Field) (M : Machine) (w : List ℕ)
    (t : ℝ) (x : Space) (ht : 1 ≤ t) :
    assemble template loading M w (point t x) = template M (point (Int.fract t) x) := by
  simp only [assemble, point_time, ite_eq_right (not_lt_of_ge ht), position_point]

theorem assemble_period_one (template : Machine → Field)
    (loading : Machine → List ℕ → Field) (M : Machine) (w : List ℕ)
    (t : ℝ) (ht : 1 ≤ t) (x : Space) :
    assemble template loading M w (point (t + 1) x) =
      assemble template loading M w (point t x) := by
  rw [assemble_after_loading template loading M w (t + 1) x (by linarith),
    assemble_after_loading template loading M w t x ht, Int.fract_add_one]

theorem assemble_input_only_in_loading (template : Machine → Field)
    (loading : Machine → List ℕ → Field) (M : Machine) (v w : List ℕ)
    (t : ℝ) (ht : 1 ≤ t) (x : Space) :
    assemble template loading M v (point t x) = assemble template loading M w (point t x) := by
  rw [assemble_after_loading template loading M v t x ht,
    assemble_after_loading template loading M w t x ht]
end PrefixFlows
end

end OAI
