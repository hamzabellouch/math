import OAI.NumberTheory.TwoPoint.Walks.ColumnRunEncoding

namespace OAI

/-! Run bits may force a split at a perfect-block boundary without changing its label. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

def columnFlagsWithCuts : List (Option α × Bool) → Option α → List (Bool × Bool)
  | [], _ => []
  | (none, _) :: rest, _ => (true, false) :: columnFlagsWithCuts rest none
  | (some a, cut) :: rest, previous =>
      (false, cut || decide (previous ≠ some a)) :: columnFlagsWithCuts rest (some a)

def columnRunHeadsWithCuts : List (Option α × Bool) → Option α → List α
  | [], _ => []
  | (none, _) :: rest, _ => columnRunHeadsWithCuts rest none
  | (some a, cut) :: rest, previous =>
      if cut = false ∧ previous = some a then columnRunHeadsWithCuts rest (some a)
      else a :: columnRunHeadsWithCuts rest (some a)

@[simp] theorem columnFlagsWithCuts_length (entries : List (Option α × Bool)) (previous : Option α) :
    (columnFlagsWithCuts entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons entry rest ih => rcases entry with ⟨a, cut⟩; cases a <;> simp [columnFlagsWithCuts, ih]

/-- A forced boundary consumes a run label even when the adjacent blocks
end and start with the same label. Arbitrary unused labels remain harmless. -/
theorem expandColumnRuns_cuts_recover (entries : List (Option CanonicalColumnLabel × Bool))
    (previous : Option CanonicalColumnLabel) (tail : List CanonicalColumnLabel) :
    expandColumnRuns (columnFlagsWithCuts entries previous)
      (columnRunHeadsWithCuts entries previous ++ tail) previous = entries.map Prod.fst := by
  induction entries generalizing previous with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨a, cut⟩
      cases a with
      | none => simpa [columnFlagsWithCuts, columnRunHeadsWithCuts, expandColumnRuns] using
          congrArg (List.cons none) (ih none)
      | some a =>
          cases cut with
          | true =>
              simpa [columnFlagsWithCuts, columnRunHeadsWithCuts, expandColumnRuns] using
                congrArg (List.cons (some a)) (ih (some a))
          | false =>
              by_cases h : previous = some a
              · subst previous
                simpa [columnFlagsWithCuts, columnRunHeadsWithCuts, expandColumnRuns] using
                  congrArg (List.cons (some a)) (ih (some a))
              · simpa [columnFlagsWithCuts, columnRunHeadsWithCuts, h, expandColumnRuns] using
                  congrArg (List.cons (some a)) (ih (some a))

end TwoPointCorrelations

end OAI
