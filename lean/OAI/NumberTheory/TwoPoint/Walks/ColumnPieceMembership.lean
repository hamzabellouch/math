import OAI.NumberTheory.TwoPoint.Walks.ColumnNameTransport
import OAI.NumberTheory.TwoPoint.Bounds.RunPartitionProperties

namespace OAI

/-! Membership information retained by the actual perfect-block cut. -/

namespace TwoPointCorrelations

variable {α β : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem columnChunkEntries_map (f : α → β) (chunks : List (List α ⊕ α)) :
    columnChunkEntries (chunks.map (Sum.map (List.map f) f)) =
      (columnChunkEntries chunks).map (fun a => (f a.1, a.2)) := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      cases chunk <;> simp only [List.map_cons, Sum.map_inl, Sum.map_inr,
        columnChunkEntries, List.flatMap_cons, Sum.elim_inl, Sum.elim_inr,
        List.map_append, List.map_map, Function.comp_def, List.map_nil] at ih ⊢ <;> rw [ih]

theorem columnRunHeads_mem_original (l : List α) (a : α)
    (ha : a ∈ columnRunHeads (l.map some) none) : a ∈ l := by
  rw [columnRunHeads_eq_destutter] at ha
  exact (List.destutter_sublist (R := (· ≠ ·)) l).subset ha

/-- A regular piece retains both its regular status and a genuinely
perfect occurrence in the original column. -/
theorem columnChunkPieces_regular_membership (omitted : α → Bool)
    (chunks : List (List α ⊕ α)) (segment : List α)
    (hs : Sum.inl segment ∈ columnChunkPieces omitted chunks) :
    segment ≠ [] ∧ ∀ a ∈ segment, omitted a = false ∧ (a, true) ∈ columnChunkEntries chunks := by
  obtain ⟨chunk, hc, hs⟩ := List.mem_flatMap.mp hs
  cases chunk with
  | inr a => simp at hs
  | inl block =>
      have hr := partitionColumnRuns_regular_entries omitted
        (columnRunHeads (block.map some) none) segment hs
      refine ⟨hr.1, ?_⟩
      intro a ha
      have hm := (partitionColumnRuns_regular_infix omitted
        (columnRunHeads (block.map some) none) segment hs).subset ha
      have hb := columnRunHeads_mem_original block a hm
      exact ⟨hr.2 a ha, List.mem_flatMap.mpr ⟨.inl block, hc, List.mem_map.mpr ⟨a, hb, rfl⟩⟩⟩

/-- Omitted runs also come from perfect positions; their separate names
therefore fit within the original occurrence-index bound. -/
theorem columnChunkPieces_omitted_membership (omitted : α → Bool)
    (chunks : List (List α ⊕ α)) (a : α)
    (ha : Sum.inr a ∈ columnChunkPieces omitted chunks) :
    omitted a = true ∧ (a, true) ∈ columnChunkEntries chunks := by
  obtain ⟨chunk, hc, ha⟩ := List.mem_flatMap.mp ha
  cases chunk with
  | inr z => simp at ha
  | inl block =>
      have hm : a ∈ (partitionColumnRuns omitted (columnRunHeads (block.map some) none)).filterMap
          (Sum.elim (fun _ => none) some) := List.mem_filterMap.mpr ⟨.inr a, ha, rfl⟩
      rw [partitionColumnRuns_omitted] at hm
      obtain ⟨hr, ho⟩ := List.mem_filter.mp hm
      have hb := columnRunHeads_mem_original block a hr
      exact ⟨ho, List.mem_flatMap.mpr ⟨.inl block, hc, List.mem_map.mpr ⟨a, hb, rfl⟩⟩⟩

omit [DecidableEq α] in
/-- A bounded list of omitted canonical names has an equally long list
of decoder indices, so no extra naming cost is introduced. -/
theorem omitted_names_lift {N : ℕ} (names : List CanonicalColumnLabel)
    (h : ∀ a ∈ names, ∃ j : Fin N, a = .omitted j.val) :
    ∃ indices : List (Fin N), indices.length = names.length ∧
      indices.map (fun j => CanonicalColumnLabel.omitted j.val) = names := by
  induction names with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons a names ih =>
      obtain ⟨j, hj⟩ := h a List.mem_cons_self
      obtain ⟨indices, hl, he⟩ := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      exact ⟨j :: indices, by simp only [List.length_cons, hl], by rw [List.map_cons, he, ← hj]⟩

end TwoPointCorrelations

end OAI
