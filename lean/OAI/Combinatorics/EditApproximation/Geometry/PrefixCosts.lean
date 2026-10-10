import OAI.Combinatorics.EditApproximation.Geometry.SharedActions
import OAI.Combinatorics.EditApproximation.Geometry.Bellman

namespace OAI

/-!
# Finite prefix costs used by the predicted bands

A prefix is a restriction of an enumerated wide action. The last jump is
evaluated at the proposed real shift. Taking the minimum over the actual
finite list, with its first member duplicated as the fallback, gives the
exact prefix minimum and its 1-Lipschitz property.
-/

namespace EditApproximation

open Finset

noncomputable def realConnectionBudget {n : ℕ} (start : ℝ) :
    List (TargetInterval n) → ℝ → ℝ
  | [], finish => |start - finish|
  | state :: rest, finish => |start - state.lo| + realConnectionBudget state.hi rest finish

theorem realConnectionBudget_finish_lipschitz {n : ℕ} (start : ℝ)
    (states : List (TargetInterval n)) (finish finish' : ℝ) :
    |realConnectionBudget start states finish - realConnectionBudget start states finish'| ≤
      |finish - finish'| := by
  induction states generalizing start with
  | nil =>
    have h := abs_abs_sub_abs_le_abs_sub (start - finish) (start - finish')
    have heq : start - finish - (start - finish') = -(finish - finish') := by ring
    simpa only [realConnectionBudget, heq, abs_neg] using h
  | cons state rest ih =>
    have heq : realConnectionBudget start (state :: rest) finish -
        realConnectionBudget start (state :: rest) finish' =
        realConnectionBudget state.hi rest finish - realConnectionBudget state.hi rest finish' := by
      simp only [realConnectionBudget]
      ring
    rw [heq]
    exact ih state.hi

theorem realConnectionBudget_cast {n : ℕ} (start finish : ℕ) (states : List (TargetInterval n)) :
    realConnectionBudget start states finish = (connectionBudget start states finish : ℝ) := by
  induction states generalizing start with
  | nil => exact natural_distance_cast start finish
  | cons state rest ih =>
    simp only [realConnectionBudget, connectionBudget, Nat.cast_add, ih,
      natural_distance_cast]

noncomputable def widePrefixCost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (p : ℝ) : ℝ :=
  realConnectionBudget r.lo ((List.ofFn states).take j)
    ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) + p) +
      ∑ i, if i.val < j then child i (states i) else 0

theorem widePrefixCost_lipschitz {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (p p' : ℝ) :
    |widePrefixCost parent r states child j p - widePrefixCost parent r states child j p'| ≤
      |p - p'| := by
  have h := realConnectionBudget_finish_lipschitz (r.lo : ℝ) ((List.ofFn states).take j)
    ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) + p)
    ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) + p')
  have heq : ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) + p) -
      ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) + p') = p - p' := by ring
  simpa only [widePrefixCost, add_sub_add_right_eq_sub, heq] using h

noncomputable def widePrefixMinimum {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (p : ℝ) : ℝ :=
  finiteMinimum (widePrefixCost parent r (actions.head hnonempty) child j p)
    (actions.map fun action => widePrefixCost parent r action child j p)

theorem widePrefixMinimum_le_member {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (p : ℝ)
    (action : Fin M → TargetInterval ny) (haction : action ∈ actions) :
    widePrefixMinimum parent r actions hnonempty child j p ≤ widePrefixCost parent r action child j p :=
  finiteMinimum_le_member _ _ (List.mem_map.mpr ⟨action, haction, rfl⟩)

theorem le_widePrefixMinimum {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (p lower : ℝ)
    (hlower : ∀ action ∈ actions, lower ≤ widePrefixCost parent r action child j p) :
    lower ≤ widePrefixMinimum parent r actions hnonempty child j p := by
  apply (le_finiteMinimum_iff _ _ _).2
  refine ⟨hlower _ (List.head_mem hnonempty), ?_⟩
  intro value hvalue
  obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hvalue
  exact hlower action ha

theorem widePrefixMinimum_lipschitz {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (p p' : ℝ) :
    |widePrefixMinimum parent r actions hnonempty child j p -
      widePrefixMinimum parent r actions hnonempty child j p'| ≤ |p - p'| := by
  have hforward (p p' : ℝ) : widePrefixMinimum parent r actions hnonempty child j p ≤
      widePrefixMinimum parent r actions hnonempty child j p' + |p - p'| := by
    apply finiteMinimum_map_spatial
    · have h := widePrefixCost_lipschitz parent r (actions.head hnonempty) child j p p'
      linarith [(abs_le.mp h).2]
    · intro action ha
      have h := widePrefixCost_lipschitz parent r action child j p p'
      linarith [(abs_le.mp h).2]
  exact abs_le.mpr ⟨by have h := hforward p' p; rw [abs_sub_comm p' p] at h; linarith,
    by linarith [hforward p p']⟩

end EditApproximation

end OAI
