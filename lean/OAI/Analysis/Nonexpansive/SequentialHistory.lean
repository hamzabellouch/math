import Mathlib.Data.List.TakeDrop

namespace OAI

/-!
# Immutable histories whose new entry is checked against the complete past

Each stored entry is legal for its exact preceding list. Later appends preserve
that past, so data chosen before current weights cannot be retrospectively
changed by removing candidates.
-/

namespace ReflexiveFixedPoints

universe u

/-- Validity records chronology, not merely membership in an unordered set. -/
inductive SequentialHistory {R : Type u} (legal : List R → R → Prop) : List R → Prop
  | nil : SequentialHistory legal []
  | snoc {past : List R} {entry : R} :
      SequentialHistory legal past → legal past entry →
        SequentialHistory legal (past ++ [entry])

namespace SequentialHistory

variable {R : Type u} {legal : List R → R → Prop}

/-- Every entry was admitted using its exact earlier prefix. -/
theorem legal_get {entries : List R} (h : SequentialHistory legal entries)
    (i : ℕ) (hi : i < entries.length) :
    legal (entries.take i) entries[i] := by
  induction h generalizing i with
  | nil => simp at hi
  | @snoc past entry history step ih =>
      by_cases hp : i < past.length
      · simpa only [List.take_append_of_le_length (Nat.le_of_lt hp), List.getElem_append_left hp]
          using ih i hp
      · have hi' : i < past.length + 1 := by
          simpa only [List.length_append, List.length_singleton] using hi
        have heq : i = past.length :=
          Nat.le_antisymm (Nat.le_of_lt_succ hi') (Nat.le_of_not_gt hp)
        subst i
        simpa only [List.take_append_of_le_length (Nat.le_refl past.length),
          List.take_length, List.getElem_append_right (Nat.le_refl past.length),
          Nat.sub_self, List.getElem_cons_zero] using step

/-- Every initial segment remains a valid history. -/
theorem take {entries : List R} (h : SequentialHistory legal entries) (n : ℕ) :
    SequentialHistory legal (entries.take n) := by
  induction n with
  | zero => simpa using (SequentialHistory.nil (legal := legal))
  | succ n ih =>
      by_cases hn : n < entries.length
      · rw [← List.take_append_getElem hn]
        exact SequentialHistory.snoc ih (h.legal_get n hn)
      · rw [List.take_of_length_le (Nat.le_trans (Nat.le_of_not_gt hn) (Nat.le_succ n))]
        exact h

end SequentialHistory

/-- A state type in which every possible state already has a legal complete history. -/
structure HistoryState (R : Type u) (legal : List R → R → Prop) where
  entries : List R
  valid : SequentialHistory legal entries

namespace HistoryState

variable {R : Type u} {legal : List R → R → Prop}

/-- Start with the empty chronological history. -/
def empty : HistoryState R legal := ⟨[], SequentialHistory.nil⟩

/-- Append one newly chosen record without changing any previous record. -/
def append (s : HistoryState R legal) (entry : R) (h : legal s.entries entry) :
    HistoryState R legal :=
  ⟨s.entries ++ [entry], SequentialHistory.snoc s.valid h⟩

@[simp] theorem append_entries (s : HistoryState R legal) (entry : R)
    (h : legal s.entries entry) :
    (s.append entry h).entries = s.entries ++ [entry] := rfl

@[simp] theorem append_length (s : HistoryState R legal) (entry : R)
    (h : legal s.entries entry) :
    (s.append entry h).entries.length = s.entries.length + 1 := by
  simp [append]

/-- Earlier records are preserved literally. -/
theorem append_get_old (s : HistoryState R legal) (entry : R)
    (h : legal s.entries entry) (i : ℕ) (hi : i < s.entries.length) :
    (s.append entry h).entries[i]'(by simpa using Nat.lt_succ_of_lt hi) = s.entries[i] := by
  exact List.getElem_append_left hi

/-- The prefix used to choose an earlier record is preserved literally. -/
theorem append_take_old (s : HistoryState R legal) (entry : R)
    (h : legal s.entries entry) (n : ℕ) (hn : n ≤ s.entries.length) :
    (s.append entry h).entries.take n = s.entries.take n :=
  List.take_append_of_le_length hn

/-- Recover the exact preceding-history law for any actual stored entry. -/
theorem legal_get (s : HistoryState R legal) (i : ℕ) (hi : i < s.entries.length) :
    legal (s.entries.take i) s.entries[i] := s.valid.legal_get i hi

end HistoryState
end ReflexiveFixedPoints

end OAI
