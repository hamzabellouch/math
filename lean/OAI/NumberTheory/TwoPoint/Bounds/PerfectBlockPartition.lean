import OAI.NumberTheory.TwoPoint.Bounds.ShortBlockPartition
import OAI.NumberTheory.TwoPoint.Bounds.RunPartitionProperties

namespace OAI

/-! Construct short perfect blocks from the actual position-status list. -/

namespace TwoPointCorrelations

variable {α β : Type*}

def initialColumnChunks (entries : List (α × Bool)) : List (List α ⊕ α) :=
  (partitionColumnRuns (fun a => !a.2) entries).map (Sum.map (List.map Prod.fst) Prod.fst)

/-- The initial cut preserves every label and its original perfect status. -/
theorem initialColumnChunks_entries (entries : List (α × Bool)) :
    columnChunkEntries (initialColumnChunks entries) = entries := by
  let raw := partitionColumnRuns (fun a : α × Bool => !a.2) entries
  have hf := partitionColumnRuns_flatten (fun a : α × Bool => !a.2) entries
  change columnChunkEntries (raw.map (Sum.map (List.map Prod.fst) Prod.fst)) = entries
  apply Eq.trans _ hf
  simp only [columnChunkEntries, List.flatMap_map]
  apply List.flatMap_congr
  intro piece hp
  cases piece with
  | inl segment =>
      have hreg := (partitionColumnRuns_regular_entries (fun a : α × Bool => !a.2)
        entries segment hp).2
      simp only [Function.comp_def, Sum.map_inl, Sum.elim_inl, List.map_map, id_eq]
      calc
        _ = segment.map id := by
          apply List.map_congr_left
          intro a ha
          have hb := hreg a ha
          cases a with
          | mk a b => cases b <;> simp_all
        _ = segment := List.map_id _
  | inr a =>
      have hom : a ∈ raw.filterMap (Sum.elim (fun _ => none) some) :=
        List.mem_filterMap.mpr ⟨.inr a, hp, rfl⟩
      rw [show raw.filterMap (Sum.elim (fun _ => none) some) =
        entries.filter (fun a => !a.2) from partitionColumnRuns_omitted _ _] at hom
      have hb := (List.mem_filter.mp hom).2
      cases a with
      | mk a b => cases b <;> simp_all [Sum.map, Function.comp_def, List.singleton]

lemma perfectChunkCount_map (f : α → β) (chunks : List (List α ⊕ α)) :
    perfectChunkCount (chunks.map (Sum.map (List.map f) f)) = perfectChunkCount chunks := by
  induction chunks with
  | nil => rfl
  | cons chunk rest ih => cases chunk <;>
      simpa [perfectChunkCount, Sum.map, List.filterMap_cons, Sum.elim] using ih

lemma perfectChunkLength_le_entries (chunks : List (List α ⊕ α)) :
    perfectChunkLength chunks ≤ (columnChunkEntries chunks).length := by
  induction chunks with
  | nil => rfl
  | cons chunk rest ih =>
      cases chunk with
      | inl l => simpa [perfectChunkLength, columnChunkEntries] using Nat.add_le_add_left ih l.length
      | inr a => simpa [perfectChunkLength, columnChunkEntries] using ih.trans (Nat.le_succ _)

/-- Each maximal perfect interval is charged to a preceding imperfect
position, except for a possible first interval. -/
theorem initialColumnChunks_count (entries : List (α × Bool)) :
    perfectChunkCount (initialColumnChunks entries) ≤
      (entries.filter (fun a => !a.2)).length + 1 := by
  unfold initialColumnChunks
  rw [perfectChunkCount_map]
  exact partitionColumnRuns_regular_count _ _

def shortPerfectColumnChunks (s : ℕ) (entries : List (α × Bool)) : List (List α ⊕ α) :=
  subdivideColumnChunks s (initialColumnChunks entries)

@[simp] theorem shortPerfectColumnChunks_entries (s : ℕ) (entries : List (α × Bool)) :
    columnChunkEntries (shortPerfectColumnChunks s entries) = entries := by
  rw [shortPerfectColumnChunks, subdivideColumnChunks_entries, initialColumnChunks_entries]

/-- This is the explicit one-half version of the manuscript's perfect-block
count. Applying it to both halves gives the stated absolute bound. -/
theorem shortPerfectColumnChunks_count (s : ℕ) (entries : List (α × Bool)) :
    perfectChunkCount (shortPerfectColumnChunks s entries) ≤
      entries.length / s + (entries.filter (fun a => !a.2)).length + 1 := by
  have h := subdivideColumnChunks_count s (initialColumnChunks entries)
  have hn := perfectChunkLength_le_entries (initialColumnChunks entries)
  rw [initialColumnChunks_entries] at hn
  have hd := Nat.div_le_div_right (c := s) hn
  have hc := initialColumnChunks_count entries
  exact h.trans (by omega)

end TwoPointCorrelations

end OAI
