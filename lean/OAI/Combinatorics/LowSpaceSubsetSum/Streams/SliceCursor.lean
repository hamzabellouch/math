import OAI.Combinatorics.LowSpaceSubsetSum.Streams.RowMerge

namespace OAI

/-!
# Cyclic row cursors into one shared immutable array

Each cursor stores its slice endpoints and the constant-size cyclic state.
Reading a row accesses the original array; it does not allocate a row array.
Empty slices have no cursor. The list slice and full trace are proof views.
-/

namespace LowSpaceSubsetSum
namespace SliceCursor

variable {α : Type*} {n : ℕ}

structure Range (n : ℕ) where
  lo : ℕ
  length : ℕ
  bounded : lo + length ≤ n
  deriving DecidableEq

structure State (n : ℕ) where
  range : Range n
  cursor : Option (CyclicCursor.State range.length)

def values (xs : Array α) (r : Range xs.size) (i : Fin r.length) : α :=
  xs[r.lo + i.val]'(by have := r.bounded; have := i.isLt; omega)

def next (xs : Array α) (s : State xs.size) : Option (α × State xs.size) :=
  match s.cursor with
  | none => none
  | some c =>
    haveI : NeZero s.range.length := ⟨by have := c.position.isLt; omega⟩
    if c.remaining = 0 then none
    else some (values xs s.range c.position, ⟨s.range, some (CyclicCursor.advance c)⟩)

def output (xs : Array α) (s : State xs.size) : List α :=
  match s.cursor with
  | none => []
  | some c =>
    haveI : NeZero s.range.length := ⟨by have := c.position.isLt; omega⟩
    CyclicCursor.trace (values xs s.range) c.remaining c

theorem reader (xs : Array α) : RowMerge.IsReader (next xs) (output xs) := by
  rintro ⟨r, c⟩
  cases c with
  | none => rfl
  | some c =>
    have : NeZero r.length := ⟨by have := c.position.isLt; omega⟩
    cases h : c.remaining with
    | zero => simp [next, output, h, CyclicCursor.trace]
    | succ k =>
      simp [next, output, h, CyclicCursor.trace, CyclicCursor.advance_remaining]

def initial (r : Range n) (pivot : ℕ) (reverse : Bool) : State n :=
  if h : 0 < r.length then
    ⟨r, some ⟨⟨pivot % r.length, Nat.mod_lt _ h⟩, r.length, reverse⟩⟩
  else ⟨r, none⟩

/-- A slice is a proof view, not a newly allocated row array. -/
def slice (xs : Array α) (r : Range xs.size) : List α := List.ofFn (values xs r)

theorem initial_perm (xs : Array α) (r : Range xs.size) (pivot : ℕ) (reverse : Bool) :
    (output xs (initial r pivot reverse)).Perm (slice xs r) := by
  by_cases h : 0 < r.length
  · have : NeZero r.length := ⟨by omega⟩
    rw [initial, dite_eq_left h]
    exact
      CyclicCursor.full_trace_perm (values xs r) ⟨pivot % r.length, Nat.mod_lt _ h⟩ reverse
  · have hz : r.length = 0 := by omega
    rw [initial, dite_eq_right h]
    simp [output, slice, hz]

theorem initial_length (xs : Array α) (r : Range xs.size) (pivot : ℕ) (reverse : Bool) :
    (output xs (initial r pivot reverse)).length = r.length := by
  rw [(initial_perm xs r pivot reverse).length_eq]
  simp [slice]

theorem slice_eq_drop_take (xs : Array α) (r : Range xs.size) :
    slice xs r = (xs.toList.drop r.lo).take r.length := by
  have hlo : r.lo ≤ xs.size := by have := r.bounded; omega
  apply List.ext_getElem
  · simp only [slice, List.length_ofFn, List.length_take, List.length_drop, Array.length_toList]
    have := r.bounded
    omega
  · intro i hi hj
    simp only [slice, List.getElem_ofFn, List.getElem_take, List.getElem_drop,
      Array.getElem_toList, values]

theorem initial_occurrences (xs : Array α) (r : Range xs.size)
    (pivot : ℕ) (reverse : Bool) :
    (output xs (initial r pivot reverse) : Multiset α) =
      ((xs.toList.drop r.lo).take r.length : Multiset α) := by
  rw [← slice_eq_drop_take xs r]
  exact Quot.sound (initial_perm xs r pivot reverse)

end SliceCursor
end LowSpaceSubsetSum

end OAI
