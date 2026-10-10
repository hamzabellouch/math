import OAI.NumberTheory.TwoPoint.Walks.ColumnDecoder

namespace OAI

/-! Reconstructing perfect runs and imperfect attachments from their bits. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- Unused segment and reference slots are harmless: they only contribute
after the encoded runs have all been emitted. -/
theorem mergeColumnRuns_append (pieces : List (List α ⊕ α))
    (padding : List Bool) (regularTail : List (List α)) (omittedTail : List α) :
    mergeColumnRuns
      (pieces.map (Sum.elim (fun _ => true) (fun _ => false)) ++ padding)
      (pieces.filterMap (Sum.elim some (fun _ => none)) ++ regularTail)
      (pieces.filterMap (Sum.elim (fun _ => none) some) ++ omittedTail) =
        pieces.flatMap (Sum.elim id List.singleton) ++
          mergeColumnRuns padding regularTail omittedTail := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih => cases piece <;>
      simp [mergeColumnRuns, List.filterMap_cons, Sum.elim, List.singleton, ih, List.append_assoc]

/-- Run boundaries reset at imperfect positions. -/
def columnFlags : List (Option α) → Option α → List (Bool × Bool)
  | [], _ => []
  | none :: rest, _ => (true, false) :: columnFlags rest none
  | some a :: rest, previous =>
      (false, decide (previous ≠ some a)) :: columnFlags rest (some a)

/-- Only the first position of each perfect constant run consumes a label. -/
def columnRunHeads : List (Option α) → Option α → List α
  | [], _ => []
  | none :: rest, _ => columnRunHeads rest none
  | some a :: rest, previous =>
      if previous = some a then columnRunHeads rest (some a)
      else a :: columnRunHeads rest (some a)

@[simp] theorem columnFlags_length (entries : List (Option α)) (previous : Option α) :
    (columnFlags entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [columnFlags, ih]

theorem columnRunHeads_length_le (entries : List (Option α)) (previous : Option α) :
    (columnRunHeads entries previous).length ≤ entries.length := by
  induction entries generalizing previous with
  | nil => simp [columnRunHeads]
  | cons a rest ih =>
      cases a with
      | none => simpa only [columnRunHeads, List.length_cons] using (ih none).trans (Nat.le_succ _)
      | some a =>
          simp only [columnRunHeads]
          split_ifs
          · exact (ih (some a)).trans (Nat.le_succ _)
          · simpa only [List.length_cons] using Nat.succ_le_succ (ih (some a))

/-- The actual boundary flags and run heads recover every perfect entry. -/
theorem expandColumnRuns_recover (entries : List (Option CanonicalColumnLabel))
    (previous : Option CanonicalColumnLabel) :
    expandColumnRuns (columnFlags entries previous) (columnRunHeads entries previous) previous =
      entries := by
  induction entries generalizing previous with
  | nil => rfl
  | cons a rest ih =>
      cases a with
      | none => simpa only [columnFlags, columnRunHeads, expandColumnRuns] using
          congrArg (List.cons none) (ih none)
      | some a =>
          by_cases h : previous = some a
          · subst previous
            simpa [columnFlags, columnRunHeads, expandColumnRuns] using
              congrArg (List.cons (some a)) (ih (some a))
          · simpa [columnFlags, columnRunHeads, h, expandColumnRuns] using
              congrArg (List.cons (some a)) (ih (some a))

/-- Extra code slots cannot affect the entries before the padding boundary. -/
theorem expandColumnRuns_take_append (flags padding : List (Bool × Bool))
    (runs : List CanonicalColumnLabel) (previous : Option CanonicalColumnLabel) :
    (expandColumnRuns (flags ++ padding) runs previous).take flags.length =
      expandColumnRuns flags runs previous := by
  induction flags generalizing runs previous with
  | nil => rfl
  | cons flag flags ih =>
      rcases flag with ⟨imperfect, boundary⟩
      cases imperfect <;> cases boundary <;> simp [expandColumnRuns, ih]

/-- Any unused regular-segment labels are ignored by the actual flag prefix. -/
theorem expandColumnRuns_recover_append (entries : List (Option CanonicalColumnLabel))
    (previous : Option CanonicalColumnLabel) (tail : List CanonicalColumnLabel) :
    expandColumnRuns (columnFlags entries previous) (columnRunHeads entries previous ++ tail)
      previous = entries := by
  induction entries generalizing previous with
  | nil => rfl
  | cons a rest ih =>
      cases a with
      | none => simpa [columnFlags, columnRunHeads, expandColumnRuns] using
          congrArg (List.cons none) (ih none)
      | some a =>
          by_cases h : previous = some a
          · subst previous
            simpa [columnFlags, columnRunHeads, expandColumnRuns] using
              congrArg (List.cons (some a)) (ih (some a))
          · simpa [columnFlags, columnRunHeads, h, expandColumnRuns] using
              congrArg (List.cons (some a)) (ih (some a))

/-- Retain labels at perfect positions only. -/
def markedColumn (label : α → CanonicalColumnLabel) (entries : List (α × Bool)) :
    List (Option CanonicalColumnLabel) :=
  entries.map (fun a => if a.2 then some (label a.1) else none)

/-- Imperfect positions store one representative each, in their original order. -/
def imperfectColumnReferences (reference : α → ℕ) (entries : List (α × Bool)) : List ℕ :=
  entries.filterMap (fun a => if a.2 then none else some (reference a.1))

/-- A reference resolves either to a perfect label or to a fresh imperfect class. -/
def resolveColumnReference (full : List (Option CanonicalColumnLabel)) (j : ℕ) :
    CanonicalColumnLabel := (full[j]?.join).getD (.freshImperfect j)

omit [DecidableEq α] in
/-- Correct local representative lookups suffice to recover the whole column,
including repetitions across different perfect blocks. -/
theorem attachImperfectLabels_recover (full : List (Option CanonicalColumnLabel))
    (label : α → CanonicalColumnLabel) (reference : α → ℕ) (entries : List (α × Bool))
    (hreference : ∀ a ∈ entries, a.2 = false →
      resolveColumnReference full (reference a.1) = label a.1) :
    attachImperfectLabels full (markedColumn label entries)
        (imperfectColumnReferences reference entries) = entries.map (fun a => label a.1) := by
  induction entries with
  | nil => rfl
  | cons a rest ih =>
      have hr : ∀ b ∈ rest, b.2 = false →
          resolveColumnReference full (reference b.1) = label b.1 :=
        fun b hb => hreference b (List.mem_cons_of_mem _ hb)
      rcases a with ⟨a, perfect⟩
      cases perfect with
      | false =>
          have ha := hreference (a, false) (List.mem_cons_self) rfl
          dsimp only [resolveColumnReference] at ha
          simpa only [markedColumn, imperfectColumnReferences, List.map_cons, List.filterMap_cons,
            Bool.false_eq_true, ↓reduceIte, attachImperfectLabels, List.headD_cons,
            List.tail_cons, ha] using
              congrArg (List.cons (label a)) (ih hr)
      | true =>
          simpa only [markedColumn, imperfectColumnReferences, List.map_cons, List.filterMap_cons,
            ↓reduceIte, attachImperfectLabels] using congrArg (List.cons (label a)) (ih hr)

omit [DecidableEq α] in
/-- Padded flags and references only affect the padded suffix, so a common
code universe can accommodate columns shorter than its vertex bound. -/
theorem attachImperfectLabels_recover_append (full : List (Option CanonicalColumnLabel))
    (label : α → CanonicalColumnLabel) (reference : α → ℕ) (entries : List (α × Bool))
    (padding : List (Option CanonicalColumnLabel)) (referenceTail : List ℕ)
    (hreference : ∀ a ∈ entries, a.2 = false →
      resolveColumnReference full (reference a.1) = label a.1) :
    attachImperfectLabels full (markedColumn label entries ++ padding)
        (imperfectColumnReferences reference entries ++ referenceTail) =
      entries.map (fun a => label a.1) ++ attachImperfectLabels full padding referenceTail := by
  induction entries with
  | nil => rfl
  | cons a rest ih =>
      have hr : ∀ b ∈ rest, b.2 = false →
          resolveColumnReference full (reference b.1) = label b.1 :=
        fun b hb => hreference b (List.mem_cons_of_mem _ hb)
      rcases a with ⟨a, perfect⟩
      cases perfect with
      | false =>
          have ha := hreference (a, false) (List.mem_cons_self) rfl
          dsimp only [resolveColumnReference] at ha
          simpa only [markedColumn, imperfectColumnReferences, List.map_cons, List.filterMap_cons,
            Bool.false_eq_true, ↓reduceIte, List.cons_append, attachImperfectLabels,
            List.headD_cons, List.tail_cons, ha] using congrArg (List.cons (label a)) (ih hr)
      | true =>
          simpa only [markedColumn, imperfectColumnReferences, List.map_cons, List.filterMap_cons,
            ↓reduceIte, List.cons_append, attachImperfectLabels] using
              congrArg (List.cons (label a)) (ih hr)

end TwoPointCorrelations

end OAI
