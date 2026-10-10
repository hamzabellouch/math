import OAI.NumberTheory.TwoPoint.Walks.ColumnBoundaryEncoding
import OAI.NumberTheory.TwoPoint.Bounds.CompressedRuns
import OAI.NumberTheory.TwoPoint.Bounds.RunPartition

namespace OAI

/-! Cutting actual perfect blocks and preserving their exact run lists. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

/-- The previous label after reading a finite part of a column. -/
def columnFinalState : List (Option α × Bool) → Option α → Option α
  | [], previous => previous
  | (a, _) :: rest, _ => columnFinalState rest a

/-- Streaming run compression composes at any cut, including imperfect entries. -/
theorem columnRunHeadsWithCuts_append (l r : List (Option α × Bool)) (previous : Option α) :
    columnRunHeadsWithCuts (l ++ r) previous =
      columnRunHeadsWithCuts l previous ++
        columnRunHeadsWithCuts r (columnFinalState l previous) := by
  induction l generalizing previous with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨a, cut⟩
      cases a with
      | none => simpa [columnRunHeadsWithCuts, columnFinalState] using ih none
      | some a =>
          simp only [List.cons_append, columnRunHeadsWithCuts, columnFinalState]
          split_ifs <;> simp only [ih, List.cons_append]

/-- Mark every entry of a perfect block, forcing its first run to start afresh. -/
def perfectBlockCuts : List α → List (Option α × Bool)
  | [] => []
  | a :: rest => (some a, true) :: rest.map (fun b => (some b, false))

theorem plainBlock_heads (l : List α) (previous : Option α) :
    columnRunHeadsWithCuts (l.map (fun a => (some a, false))) previous =
      columnRunHeads (l.map some) previous := by
  induction l generalizing previous with
  | nil => rfl
  | cons a rest ih =>
      by_cases h : previous = some a <;> simp [columnRunHeadsWithCuts, columnRunHeads, h, ih]

/-- A perfect block has its usual compressed run list regardless of the
label just before it. Thus equal labels across block boundaries stay distinct runs. -/
theorem perfectBlockCuts_heads (l : List α) (previous : Option α) :
    columnRunHeadsWithCuts (perfectBlockCuts l) previous =
      columnRunHeads (l.map some) none := by
  cases l with
  | nil => rfl
  | cons a rest => simp [perfectBlockCuts, columnRunHeadsWithCuts, columnRunHeads, plainBlock_heads]

/-- An actual column is a sequence of perfect blocks and individual imperfect entries. -/
def columnChunkCuts (chunks : List (List α ⊕ α)) : List (Option α × Bool) :=
  chunks.flatMap (Sum.elim perfectBlockCuts (fun _ => [(none, false)]))

def columnChunkEntries (chunks : List (List α ⊕ α)) : List (α × Bool) :=
  chunks.flatMap (Sum.elim (fun l => l.map (fun a => (a, true))) (fun a => [(a, false)]))

def columnChunkRuns (chunks : List (List α ⊕ α)) : List α :=
  chunks.flatMap (Sum.elim (fun l => columnRunHeads (l.map some) none) (fun _ => []))

omit [DecidableEq α] in
theorem perfectBlockCuts_values (l : List α) :
    (perfectBlockCuts l).map Prod.fst = l.map some := by
  cases l <;> simp [perfectBlockCuts, List.map_map, Function.comp_def]

omit [DecidableEq α] in
theorem columnChunkCuts_values (chunks : List (List α ⊕ α)) :
    (columnChunkCuts chunks).map Prod.fst =
      (columnChunkEntries chunks).map (fun a => if a.2 then some a.1 else none) := by
  induction chunks with
  | nil => rfl
  | cons chunk rest ih =>
      cases chunk <;>
        simp [columnChunkCuts, columnChunkEntries, Sum.elim, perfectBlockCuts_values,
          List.map_map, Function.comp_def] at ih ⊢ <;> exact ih

/-- Compression of the assembled column is exactly the concatenation of
its independently compressed perfect blocks. -/
theorem columnChunkCuts_heads (chunks : List (List α ⊕ α)) (previous : Option α) :
    columnRunHeadsWithCuts (columnChunkCuts chunks) previous = columnChunkRuns chunks := by
  induction chunks generalizing previous with
  | nil => rfl
  | cons chunk rest ih =>
      cases chunk with
      | inl block =>
          change columnRunHeadsWithCuts (perfectBlockCuts block ++ columnChunkCuts rest) previous =
            columnRunHeads (block.map some) none ++ columnChunkRuns rest
          rw [columnRunHeadsWithCuts_append, perfectBlockCuts_heads, ih]
      | inr a =>
          simpa [columnChunkCuts, columnRunHeadsWithCuts, columnChunkRuns] using ih none

/-- Apply the omitted-label cut to every actual compressed perfect block. -/
def columnChunkPieces (omitted : α → Bool) (chunks : List (List α ⊕ α)) :
    List (List α ⊕ α) :=
  chunks.flatMap (Sum.elim
    (fun l => partitionColumnRuns omitted (columnRunHeads (l.map some) none)) (fun _ => []))

theorem columnChunkPieces_flatten (omitted : α → Bool) (chunks : List (List α ⊕ α)) :
    (columnChunkPieces omitted chunks).flatMap (Sum.elim id List.singleton) =
      columnRunHeadsWithCuts (columnChunkCuts chunks) none := by
  rw [columnChunkCuts_heads]
  induction chunks with
  | nil => rfl
  | cons chunk rest ih =>
      cases chunk <;>
        simp [columnChunkPieces, columnChunkRuns, Sum.elim, List.flatMap_append,
          partitionColumnRuns_flatten] at ih ⊢ <;> exact ih

end TwoPointCorrelations

end OAI
