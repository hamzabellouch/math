import OAI.NumberTheory.TwoPoint.Walks.ColumnChunks
import Mathlib.Data.Finset.Card

namespace OAI

/-! Exact decoder budgets for lists of actual perfect blocks. -/

namespace TwoPointCorrelations

open Finset

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
@[simp] theorem regularPieceCount_append (a b : List (List α ⊕ α)) :
    regularPieceCount (a ++ b) = regularPieceCount a + regularPieceCount b := by
  simp [regularPieceCount, List.filterMap_append]

omit [DecidableEq α] in
@[simp] theorem omittedPieceCount_append (a b : List (List α ⊕ α)) :
    omittedPieceCount (a ++ b) = omittedPieceCount a + omittedPieceCount b := by
  simp [omittedPieceCount, List.filterMap_append]

/-- Interval-shaped label occurrences imply the concrete omitted-run budget. -/
theorem block_omitted_piece_budget (l : List α) (omitted : Finset α)
    (hinterval : ∀ i j k : Fin l.length, i ≤ j → j ≤ k →
      l.get i = l.get k → l.get j = l.get i) :
    omittedPieceCount (partitionColumnRuns (fun a => decide (a ∈ omitted))
      (columnRunHeads (l.map some) none)) ≤ omitted.card := by
  let runs := columnRunHeads (l.map some) none
  have hn : (runs.filter (fun a => decide (a ∈ omitted))).Nodup :=
    (columnRunHeads_nodup l hinterval).filter _
  change ((partitionColumnRuns _ runs).filterMap _).length ≤ _
  rw [partitionColumnRuns_omitted, ← List.toFinset_card_of_nodup hn]
  apply card_le_card
  intro a ha
  exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp ha)).2

theorem block_regular_piece_budget (l : List α) (omitted : Finset α)
    (hinterval : ∀ i j k : Fin l.length, i ≤ j → j ≤ k →
      l.get i = l.get k → l.get j = l.get i) :
    regularPieceCount (partitionColumnRuns (fun a => decide (a ∈ omitted))
      (columnRunHeads (l.map some) none)) ≤ omitted.card + 1 := by
  have ho := block_omitted_piece_budget l omitted hinterval
  have hr := partitionColumnRuns_regular_count (fun a => decide (a ∈ omitted))
    (columnRunHeads (l.map some) none)
  have he := congrArg List.length (partitionColumnRuns_omitted
    (fun a => decide (a ∈ omitted)) (columnRunHeads (l.map some) none))
  change omittedPieceCount _ = _ at he
  omega

def perfectChunkCount (chunks : List (List α ⊕ α)) : ℕ :=
  (chunks.filterMap (Sum.elim some (fun _ => none))).length

/-- Across actual perfect blocks, each omitted class is charged only once
per block, and every regular segment is charged to an omitted run or a block start. -/
theorem columnChunk_piece_budgets (chunks : List (List α ⊕ α)) (omitted : Finset α)
    (hinterval : ∀ l, Sum.inl l ∈ chunks → ∀ i j k : Fin l.length, i ≤ j → j ≤ k →
      l.get i = l.get k → l.get j = l.get i) :
    omittedPieceCount (columnChunkPieces (fun a => decide (a ∈ omitted)) chunks) ≤
        omitted.card * perfectChunkCount chunks ∧
    regularPieceCount (columnChunkPieces (fun a => decide (a ∈ omitted)) chunks) ≤
        (omitted.card + 1) * perfectChunkCount chunks := by
  induction chunks with
  | nil => simp [columnChunkPieces, perfectChunkCount, omittedPieceCount, regularPieceCount]
  | cons chunk rest ih =>
      have hir := ih (fun l hl => hinterval l (List.mem_cons_of_mem _ hl))
      cases chunk with
      | inl l =>
          have ho := block_omitted_piece_budget l omitted (hinterval l (List.mem_cons_self))
          have hr := block_regular_piece_budget l omitted (hinterval l (List.mem_cons_self))
          simp only [columnChunkPieces, List.flatMap_cons, Sum.elim_inl,
            omittedPieceCount_append, regularPieceCount_append]
          change _ ≤ omitted.card * (perfectChunkCount rest + 1) ∧
            _ ≤ (omitted.card + 1) * (perfectChunkCount rest + 1)
          constructor
          · change omittedPieceCount (partitionColumnRuns _ _) +
              omittedPieceCount (columnChunkPieces _ rest) ≤ _
            calc
              _ ≤ omitted.card + omitted.card * perfectChunkCount rest := Nat.add_le_add ho hir.1
              _ = _ := by ring
          · change regularPieceCount (partitionColumnRuns _ _) +
              regularPieceCount (columnChunkPieces _ rest) ≤ _
            calc
              _ ≤ (omitted.card + 1) + (omitted.card + 1) * perfectChunkCount rest :=
                Nat.add_le_add hr hir.2
              _ = _ := by ring
      | inr a =>
          simpa [columnChunkPieces, perfectChunkCount, List.filterMap_cons, Sum.elim] using hir

/-- The full merge mask fits in the original column length. -/
theorem columnChunkPieces_length_le (omitted : α → Bool) (chunks : List (List α ⊕ α)) :
    (columnChunkPieces omitted chunks).length ≤ (columnChunkEntries chunks).length := by
  induction chunks with
  | nil => rfl
  | cons chunk rest ih =>
      cases chunk with
      | inl l =>
          have hl := (partitionColumnRuns_length_le omitted (columnRunHeads (l.map some) none)).trans
            (columnRunHeads_length_le (l.map some) none)
          simp only [List.length_map] at hl
          simpa only [columnChunkPieces, columnChunkEntries, List.flatMap_cons, Sum.elim_inl,
            List.length_append, List.length_map] using Nat.add_le_add hl ih
      | inr a =>
          simpa [columnChunkPieces, columnChunkEntries] using ih.trans (Nat.le_succ _)

end TwoPointCorrelations

end OAI
