import OAI.NumberTheory.TwoPoint.Bounds.PerfectBlockPartition
import OAI.NumberTheory.TwoPoint.Walks.IndexedRuns

namespace OAI

/-! The constructed perfect blocks are actual contiguous intervals of positions. -/

namespace TwoPointCorrelations

variable {α : Type*}

theorem subdivideColumnChunks_regular_origin (s : ℕ) (chunks : List (List α ⊕ α))
    (block : List α) (hb : Sum.inl block ∈ subdivideColumnChunks s chunks) :
    ∃ large, Sum.inl large ∈ chunks ∧ block ∈ shortBlocks s large := by
  obtain ⟨piece, hp, hb⟩ := List.mem_flatMap.mp hb
  cases piece with
  | inl large =>
      simp only [Sum.elim_inl, List.mem_map, Sum.inl.injEq] at hb
      obtain ⟨l, hl, rfl⟩ := hb
      exact ⟨large, hp, hl⟩
  | inr a => simp at hb

theorem initialColumnChunks_regular_origin (entries : List (α × Bool))
    (block : List α) (hb : Sum.inl block ∈ initialColumnChunks entries) :
    ∃ raw, Sum.inl raw ∈ partitionColumnRuns (fun a : α × Bool => !a.2) entries ∧
      block = raw.map Prod.fst := by
  obtain ⟨piece, hp, he⟩ := List.mem_map.mp hb
  cases piece with
  | inl raw =>
      simp only [Sum.map_inl, Sum.inl.injEq] at he
      exact ⟨raw, hp, he.symm⟩
  | inr a => simp at he

/-- Every constructed block is a contiguous part of the original column,
and all its positions have their original perfect status. -/
theorem shortPerfectColumnChunks_regular_positions (s : ℕ) (entries : List (α × Bool))
    (block : List α) (hb : Sum.inl block ∈ shortPerfectColumnChunks s entries) :
    block.IsInfix (entries.map Prod.fst) ∧ ∀ a ∈ block, (a, true) ∈ entries := by
  obtain ⟨large, hl, hsub⟩ := subdivideColumnChunks_regular_origin s
    (initialColumnChunks entries) block hb
  obtain ⟨raw, hr, rfl⟩ := initialColumnChunks_regular_origin entries large hl
  have hi := partitionColumnRuns_regular_infix (fun a : α × Bool => !a.2) entries raw hr
  have hs := shortBlocks_infix s (raw.map Prod.fst) block hsub
  refine ⟨hs.trans (hi.map Prod.fst), ?_⟩
  intro a ha
  obtain ⟨p, hp, he⟩ := List.mem_map.mp (hs.subset ha)
  have hpreg := (partitionColumnRuns_regular_entries (fun a : α × Bool => !a.2) entries raw hr).2 p hp
  have hmem := hi.subset hp
  rcases p with ⟨b, perfect⟩
  cases perfect <;> simp_all

/-- A prefix of the position-indexed label list is the same label list
with the shortened length. -/
theorem blockLabelList_take (label : ℕ → α) (start total len : ℕ) (h : len ≤ total) :
    (blockLabelList label start total).take len = blockLabelList label start len := by
  induction len generalizing start total with
  | zero => simp [blockLabelList]
  | succ len ih =>
      cases total with
      | zero => omega
      | succ total =>
          rw [blockLabelList_succ, blockLabelList_succ, List.take_succ_cons, ih]
          omega

theorem blockLabelList_drop_take (label : ℕ → α) (start total a len : ℕ)
    (h : a + len ≤ total) :
    ((blockLabelList label start total).drop a).take len = blockLabelList label (start + a) len := by
  induction a generalizing start total with
  | zero => simpa using blockLabelList_take label start total len (by simpa using h)
  | succ a ih =>
      cases total with
      | zero => omega
      | succ total =>
          rw [blockLabelList_succ, List.drop_succ_cons, ih (start + 1) total (by omega)]
          congr 1
          omega

/-- Every contiguous part of a position-indexed list has an actual bounded
starting index, so no extra run-position data need be postulated. -/
theorem infix_blockLabelList_positions (label : ℕ → α) (start total : ℕ)
    (block : List α) (hb : block.IsInfix (blockLabelList label start total)) :
    ∃ a, a + block.length ≤ total ∧ block = blockLabelList label (start + a) block.length := by
  obtain ⟨before, after, he⟩ := hb
  have hlen : before.length + block.length ≤ total := by
    have ht := congrArg List.length he
    simp only [List.length_append, blockLabelList, List.length_map, List.length_range] at ht
    omega
  refine ⟨before.length, hlen, ?_⟩
  rw [← blockLabelList_drop_take label start total before.length block.length hlen, ← he]
  simp

/-- Each short block has the promised maximum length. -/
theorem shortPerfectColumnChunks_regular_size (s : ℕ) (hs : 0 < s)
    (entries : List (α × Bool)) (block : List α)
    (hb : Sum.inl block ∈ shortPerfectColumnChunks s entries) : block.length ≤ s := by
  obtain ⟨large, _, hsub⟩ := subdivideColumnChunks_regular_origin s
    (initialColumnChunks entries) block hb
  exact shortBlocks_size s hs large block hsub

/-- On the actual consecutive position list, every generated block has a
bounded starting index and contains only perfect positions. -/
theorem shortPerfectColumnChunks_position_intervals (N s : ℕ) (perfect : ℕ → Bool)
    (block : List ℕ)
    (hb : Sum.inl block ∈ shortPerfectColumnChunks s
      ((List.range N).map (fun i => (i, perfect i)))) :
    ∃ start, start + block.length ≤ N ∧
      block = (List.range block.length).map (fun i => start + i) ∧
      ∀ i ∈ block, perfect i = true := by
  obtain ⟨hinfix, hperfect⟩ := shortPerfectColumnChunks_regular_positions s _ block hb
  have hi : block.IsInfix (blockLabelList id 0 N) := by
    simpa [blockLabelList, List.map_map, Function.comp_def] using hinfix
  obtain ⟨start, hbound, hblock⟩ := infix_blockLabelList_positions id 0 N block hi
  refine ⟨start, hbound, ?_, ?_⟩
  · simpa [blockLabelList] using hblock
  · intro i hi
    obtain ⟨j, _, heq⟩ := List.mem_map.mp (hperfect i hi)
    have hji : j = i := congrArg Prod.fst heq
    simpa only [hji] using congrArg Prod.snd heq

end TwoPointCorrelations

end OAI
