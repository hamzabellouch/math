import OAI.NumberTheory.TwoPoint.Walks.ColumnChunkBudgets
import Mathlib.Data.List.SplitLengths

namespace OAI

/-! The actual subdivision of perfect intervals into short blocks. -/

namespace TwoPointCorrelations

variable {α : Type*}

def shortBlockLengths (n s : ℕ) : List ℕ := List.replicate (n / s) s ++ [n % s]

lemma shortBlockLengths_sum (n s : ℕ) : (shortBlockLengths n s).sum = n := by
  simpa [shortBlockLengths, Nat.mul_comm] using Nat.div_add_mod n s

def shortBlocks (s : ℕ) (l : List α) : List (List α) :=
  (shortBlockLengths l.length s).splitLengths l

@[simp] theorem shortBlocks_flatten (s : ℕ) (l : List α) : (shortBlocks s l).flatten = l := by
  exact List.flatten_splitLengths l _ (by rw [shortBlockLengths_sum])

@[simp] theorem shortBlocks_length (s : ℕ) (l : List α) :
    (shortBlocks s l).length = l.length / s + 1 := by
  simp [shortBlocks, shortBlockLengths]

theorem shortBlocks_size (s : ℕ) (hs : 0 < s) (l : List α) :
    ∀ block ∈ shortBlocks s l, block.length ≤ s := by
  apply List.length_mem_splitLengths
  intro n hn
  simp only [shortBlockLengths, List.mem_append, List.mem_replicate, List.mem_singleton] at hn
  rcases hn with ⟨_, rfl⟩ | rfl
  · exact le_rfl
  · exact (Nat.mod_lt _ hs).le

theorem shortBlocks_infix (s : ℕ) (l block : List α) (hb : block ∈ shortBlocks s l) :
    block.IsInfix l := by
  have h := List.infix_of_mem_flatten hb
  rwa [shortBlocks_flatten] at h

/-- Imperfect positions stay single; perfect intervals are split into
full blocks of size `s` and one possible final shorter block. Empty final
blocks are harmless and are included in the upper bound. -/
def subdivideColumnChunks (s : ℕ) (chunks : List (List α ⊕ α)) : List (List α ⊕ α) :=
  chunks.flatMap (Sum.elim (fun l => (shortBlocks s l).map Sum.inl) (fun a => [Sum.inr a]))

lemma columnChunkEntries_map_inl (blocks : List (List α)) :
    columnChunkEntries (blocks.map Sum.inl) = blocks.flatten.map (fun a => (a, true)) := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      simpa [columnChunkEntries, Sum.elim, List.map_append] using
        congrArg (List.append (block.map (fun a => (a, true)))) ih

lemma columnChunkEntries_append (a b : List (List α ⊕ α)) :
    columnChunkEntries (a ++ b) = columnChunkEntries a ++ columnChunkEntries b := by
  simp [columnChunkEntries, List.flatMap_append]

/-- Subdivision preserves every position, including its perfect/imperfect status. -/
theorem subdivideColumnChunks_entries (s : ℕ) (chunks : List (List α ⊕ α)) :
    columnChunkEntries (subdivideColumnChunks s chunks) = columnChunkEntries chunks := by
  induction chunks with
  | nil => rfl
  | cons chunk rest ih =>
      cases chunk with
      | inl l =>
          change columnChunkEntries ((shortBlocks s l).map Sum.inl ++ subdivideColumnChunks s rest) =
            l.map (fun a => (a, true)) ++ columnChunkEntries rest
          rw [columnChunkEntries_append, columnChunkEntries_map_inl, shortBlocks_flatten, ih]
      | inr a =>
          simpa [subdivideColumnChunks, columnChunkEntries] using
            congrArg (List.cons (a, false)) ih

def perfectChunkLength (chunks : List (List α ⊕ α)) : ℕ :=
  (chunks.map (Sum.elim List.length (fun _ => 0))).sum

lemma perfectChunkCount_append (a b : List (List α ⊕ α)) :
    perfectChunkCount (a ++ b) = perfectChunkCount a + perfectChunkCount b := by
  simp [perfectChunkCount, List.filterMap_append]

lemma perfectChunkCount_map_inl (blocks : List (List α)) :
    perfectChunkCount (blocks.map Sum.inl) = blocks.length := by
  simp [perfectChunkCount, List.filterMap_map, Function.comp_def, Sum.elim]

/-- The number of short perfect blocks is at most the total perfect length
 divided by the block size, plus the number of original perfect intervals. -/
theorem subdivideColumnChunks_count (s : ℕ) (chunks : List (List α ⊕ α)) :
    perfectChunkCount (subdivideColumnChunks s chunks) ≤
      perfectChunkLength chunks / s + perfectChunkCount chunks := by
  induction chunks with
  | nil => simp [subdivideColumnChunks, perfectChunkCount, perfectChunkLength]
  | cons chunk rest ih =>
      cases chunk with
      | inl l =>
          have hd := Nat.div_add_div_le_add_div (x := l.length) (y := perfectChunkLength rest) (z := s)
          change perfectChunkCount ((shortBlocks s l).map Sum.inl ++ subdivideColumnChunks s rest) ≤
            (l.length + perfectChunkLength rest) / s + (perfectChunkCount rest + 1)
          rw [perfectChunkCount_append, perfectChunkCount_map_inl, shortBlocks_length]
          omega
      | inr a =>
          simpa [subdivideColumnChunks, perfectChunkCount, perfectChunkLength, Sum.elim,
            List.filterMap_cons] using ih

end TwoPointCorrelations

end OAI
