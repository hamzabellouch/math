import OAI.Combinatorics.LowSpaceSubsetSum.Streams.SliceCursor

namespace OAI

/-! # Attach one fixed first-array occurrence to a shared-array row reader -/

namespace LowSpaceSubsetSum
namespace PairCursor

variable {α β : Type*}

structure State (α : Type*) (n : ℕ) where
  left : α
  cursor : SliceCursor.State n

def next (xs : Array β) (s : State α xs.size) : Option ((α × β) × State α xs.size) :=
  (SliceCursor.next xs s.cursor).map (fun z => ((s.left, z.1), ⟨s.left, z.2⟩))

def output (xs : Array β) (s : State α xs.size) : List (α × β) :=
  (SliceCursor.output xs s.cursor).map (fun y => (s.left, y))

theorem reader (xs : Array β) : RowMerge.IsReader (next (α := α) xs) (output xs) := by
  intro s
  have hr := SliceCursor.reader xs s.cursor
  cases h : SliceCursor.next xs s.cursor with
  | none =>
    simp only [h] at hr
    simp only [next, h, Option.map_none, output, hr, List.map_nil]
  | some z =>
    obtain ⟨y, c⟩ := z
    simp only [h] at hr
    simp only [next, h, Option.map_some, output, hr, List.map_cons]

end PairCursor
end LowSpaceSubsetSum

end OAI
