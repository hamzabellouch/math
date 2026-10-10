import OAI.Combinatorics.EditApproximation.Geometry.Connections

namespace OAI

/-!
# Preservation of the two action lower bounds

The action invariant follows from actual edit and shift connection
inequalities, rather than an assumed lower-bound-preserving oracle.
-/

namespace EditApproximation

open EditDistortion

theorem list_sum_map_le {ι : Type*} (entries : List ι) (f g : ι → ℝ)
    (h : ∀ i ∈ entries, f i ≤ g i) : (entries.map f).sum ≤ (entries.map g).sum := by
  induction entries with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

theorem list_sum_map_div {ι : Type*} (entries : List ι) (f : ι → ℝ) (a : ℝ) :
    (entries.map fun i => f i / a).sum = (entries.map f).sum / a := by
  induction entries with
  | nil => simp
  | cons i rest ih => simp only [List.map_cons, List.sum_cons, ih, add_div]

theorem actual_action_lower {α : Type*} (word : List α)
    (children : List (List α × TargetInterval word.length))
    (parent : TargetInterval word.length) (a : ℝ) (ha : 1 ≤ a)
    (value : (List α × TargetInterval word.length) → ℝ)
    (hcost : ∀ child ∈ children,
      (edit child.1 (substring word child.2.lo child.2.hi) : ℝ) / a ≤ value child)
    (hgap : ∀ child ∈ children,
      |signedLengthGap child.1 (substring word child.2.lo child.2.hi)| ≤ value child) :
    max ((edit (children.map Prod.fst).flatten (substring word parent.lo parent.hi) : ℝ) / a)
        |signedLengthGap (children.map Prod.fst).flatten (substring word parent.lo parent.hi)| ≤
      (connectionBudget parent.lo (children.map Prod.snd) parent.hi : ℝ) +
        (children.map value).sum := by
  have ha0 : 0 < a := by linarith
  let conn : ℝ := connectionBudget parent.lo (children.map Prod.snd) parent.hi
  have hconn0 : 0 ≤ conn := Nat.cast_nonneg _
  have hconnDiv : conn / a ≤ conn := by
    apply (div_le_iff₀ ha0).2
    nlinarith
  apply max_le
  · have hconnection :
        (edit (children.map Prod.fst).flatten (substring word parent.lo parent.hi) : ℝ) ≤
          (children.map fun child =>
            (edit child.1 (substring word child.2.lo child.2.hi) : ℝ)).sum + conn := by
      dsimp only [conn]
      have hcast (entries : List (List α × TargetInterval word.length)) :
          (((entries.map fun child =>
            edit child.1 (substring word child.2.lo child.2.hi)).sum : ℕ) : ℝ) =
            (entries.map fun child =>
              (edit child.1 (substring word child.2.lo child.2.hi) : ℝ)).sum := by
        induction entries with
        | nil => simp
        | cons child rest ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
      rw [← hcast]
      exact_mod_cast child_connection_bound word children parent
    have hdivide := div_le_div_of_nonneg_right hconnection ha0.le
    rw [add_div] at hdivide
    have hsum := list_sum_map_le children _ value hcost
    rw [list_sum_map_div] at hsum
    linarith
  · have hconnection := child_shift_connection_bound word children parent
    have hsum := list_sum_map_le children _ value hgap
    change _ ≤ conn + _
    linarith

end EditApproximation

end OAI
