import OAI.NumberTheory.TwoPoint.Walks.IndexedBlockFamily
import OAI.NumberTheory.TwoPoint.Walks.ColumnNameTransport

namespace OAI

/-! Identify the shared indexed path family with the actual decoder pieces. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

theorem columnChunkPieces_via_blocks (omitted : α → Bool) (chunks : List (List α ⊕ α)) :
    columnChunkPieces omitted chunks =
      (chunks.filterMap (Sum.elim some (fun _ => none))).flatMap
        (fun block => partitionColumnRuns omitted (columnRunHeads (block.map some) none)) := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      cases chunk with
      | inl block =>
          simpa only [columnChunkPieces, List.flatMap_cons, List.filterMap_cons, Sum.elim_inl] using
            congrArg (fun rest => partitionColumnRuns omitted
              (columnRunHeads (block.map some) none) ++ rest) ih
      | inr a =>
          simpa only [columnChunkPieces, List.flatMap_cons, List.filterMap_cons,
            Sum.elim_inr, List.nil_append] using ih

theorem columnChunkPieces_from_intervals (label : ℕ → α) (omitted : α → Bool)
    (chunks : List (List α ⊕ α)) (blocks : List (ℕ × ℕ))
    (hblocks : chunks.filterMap (Sum.elim some (fun _ => none)) =
      blocks.map (fun b => blockLabelList label b.1 b.2)) :
    columnChunkPieces omitted chunks = blocks.flatMap (fun b =>
      partitionColumnRuns omitted (columnRunHeads ((blockLabelList label b.1 b.2).map some) none)) := by
  rw [columnChunkPieces_via_blocks, hblocks, List.flatMap_map]

/-- Forgetting the stored run-start indices gives exactly the regular
piece list consumed by the column decoder, in the same order. -/
theorem indexedRegularSegments_labels (label : ℕ → α) (omitted : α → Bool)
    (blocks : List (ℕ × ℕ)) :
    (indexedRegularSegments label omitted blocks).map (List.map Prod.snd) =
      (blocks.flatMap (fun b => partitionColumnRuns omitted
        (columnRunHeads ((blockLabelList label b.1 b.2).map some) none))).filterMap
          (Sum.elim some (fun _ => none)) := by
  induction blocks with
  | nil => rfl
  | cons b blocks ih =>
      change ((_ ++ indexedRegularSegments label omitted blocks).map (List.map Prod.snd)) = _
      rw [List.map_append]
      simp only [List.flatMap_cons, List.filterMap_append]
      rw [ih]
      congr 1
      rw [← mapped_pieces_regular, indexedBlockRuns_partition]

theorem indexedRegularSegments_eq_regular_pieces (label : ℕ → α) (omitted : α → Bool)
    (chunks : List (List α ⊕ α)) (blocks : List (ℕ × ℕ))
    (hblocks : chunks.filterMap (Sum.elim some (fun _ => none)) =
      blocks.map (fun b => blockLabelList label b.1 b.2)) :
    (indexedRegularSegments label omitted blocks).map (List.map Prod.snd) =
      (columnChunkPieces omitted chunks).filterMap (Sum.elim some (fun _ => none)) := by
  rw [columnChunkPieces_from_intervals label omitted chunks blocks hblocks]
  exact indexedRegularSegments_labels label omitted blocks

omit [DecidableEq α] in
/-- Every original perfect occurrence belongs to one of the actual perfect
blocks. This includes occurrences immediately next to imperfect positions. -/
theorem perfect_entry_mem_block (chunks : List (List α ⊕ α)) (a : α)
    (ha : (a, true) ∈ columnChunkEntries chunks) :
    ∃ block, Sum.inl block ∈ chunks ∧ a ∈ block := by
  obtain ⟨chunk, hc, ha⟩ := List.mem_flatMap.mp ha
  cases chunk with
  | inl block =>
      obtain ⟨b, hb, heq⟩ := List.mem_map.mp ha
      have he : b = a := congrArg Prod.fst heq
      exact ⟨block, hc, he ▸ hb⟩
  | inr b =>
      have heq := List.mem_singleton.mp ha
      have hfalse : false = true := (congrArg Prod.snd heq).symm
      contradiction

/-- Every regular perfect label appears in the actual indexed path family. -/
theorem perfect_regular_entry_covered (label : ℕ → α) (omitted : α → Bool)
    (chunks : List (List α ⊕ α)) (blocks : List (ℕ × ℕ))
    (hblocks : chunks.filterMap (Sum.elim some (fun _ => none)) =
      blocks.map (fun b => blockLabelList label b.1 b.2))
    (a : α) (ha : (a, true) ∈ columnChunkEntries chunks) (hr : omitted a = false) :
    ∃ segment ∈ indexedRegularSegments label omitted blocks, ∃ p ∈ segment, p.2 = a := by
  obtain ⟨block, hb, hab⟩ := perfect_entry_mem_block chunks a ha
  have hm : block ∈ chunks.filterMap (Sum.elim some (fun _ => none)) :=
    List.mem_filterMap.mpr ⟨.inl block, hb, rfl⟩
  rw [hblocks] at hm
  obtain ⟨b, hbb, he⟩ := List.mem_map.mp hm
  apply indexedRegularSegments_cover label omitted blocks b hbb a _ hr
  rwa [he]

end TwoPointCorrelations

end OAI
