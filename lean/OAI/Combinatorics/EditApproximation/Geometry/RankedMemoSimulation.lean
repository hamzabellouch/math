import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoProgram

namespace OAI

/-! Local recurrence equalities identify the complete table semantics
of a lazy query program. No complete table is evaluated by the memo
interpreter; it is used only as the mathematical specification. -/

namespace EditApproximation

theorem rankedProgramValue_eq {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (expected : κ → ℚ)
    (hstep : ∀ key, (program key).value (fun child => expected child.val) = expected key)
    (key : κ) : rankedProgramValue rank program key = expected key := by
  have hall : ∀ level key, rank key = level → rankedProgramValue rank program key = expected key := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel
      rw [rankedProgramValue]
      have hchildren : (fun child : {child : κ // rank child < rank key} =>
          rankedProgramValue rank program child.val) = fun child => expected child.val := by
        funext child
        exact ih (rank child.val) (hlevel ▸ child.property) child.val rfl
      rw [hchildren]
      exact hstep key
  exact hall (rank key) key rfl

theorem rankedMemoEvaluate_specification {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (expected : κ → ℚ)
    (hstep : ∀ key, (program key).value (fun child => expected child.val) = expected key)
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) :
    (rankedMemoEvaluate rank program bits encode key .empty).value = expected key :=
  (rankedMemoEvaluate_empty rank program bits encode hinjective hbounded key).trans
    (rankedProgramValue_eq rank program expected hstep key)

end EditApproximation

end OAI
