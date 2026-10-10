import OAI.NumberTheory.TwoPoint.Walks.ColumnChunks

namespace OAI

/-! Transport the actual run decomposition to its canonical class names. -/

namespace TwoPointCorrelations

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem columnRunHeads_map (f : α → β) (l : List α)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b ↔ a = b) :
    (columnRunHeads (l.map some) none).map f =
      columnRunHeads ((l.map f).map some) none := by
  rw [columnRunHeads_eq_destutter, columnRunHeads_eq_destutter]
  exact List.map_destutter (fun a ha b hb => not_congr (hinj a ha b hb).symm)

theorem columnChunkRuns_map (f : α → β) (chunks : List (List α ⊕ α))
    (hinj : ∀ l, Sum.inl l ∈ chunks → ∀ a ∈ l, ∀ b ∈ l, f a = f b ↔ a = b) :
    (columnChunkRuns chunks).map f =
      columnChunkRuns (chunks.map (Sum.map (List.map f) f)) := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      have hi := ih (fun l hl => hinj l (List.mem_cons_of_mem _ hl))
      cases chunk with
      | inl l =>
          simp only [List.map_cons, Sum.map_inl, columnChunkRuns, List.flatMap_cons,
            Sum.elim_inl, List.map_append]
          rw [columnRunHeads_map f l (hinj l List.mem_cons_self)]
          exact congrArg (fun tail => columnRunHeads ((l.map f).map some) none ++ tail) hi
      | inr a => simpa only [columnChunkRuns, List.flatMap_cons, Sum.elim_inr, List.map_nil,
          List.nil_append, List.map_cons, Sum.map_inr] using hi

omit [DecidableEq α] [DecidableEq β] in
theorem mapped_pieces_flatten (f : α → β) (pieces : List (List α ⊕ α)) :
    (pieces.map (Sum.map (List.map f) f)).flatMap (Sum.elim id List.singleton) =
      (pieces.flatMap (Sum.elim id List.singleton)).map f := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
      cases piece <;> simp only [List.map_cons, Sum.map_inl, Sum.map_inr,
        List.flatMap_cons, Sum.elim_inl, Sum.elim_inr, List.map_append,
        id_eq] <;> rw [ih]
      all_goals simp only [List.singleton, List.map_cons, List.map_nil]

/-- Canonical renaming preserves the exact merge list when it preserves
the equality relation on each actual block. -/
theorem mapped_column_pieces_heads (f : α → β) (omitted : α → Bool)
    (chunks : List (List α ⊕ α))
    (hinj : ∀ l, Sum.inl l ∈ chunks → ∀ a ∈ l, ∀ b ∈ l, f a = f b ↔ a = b) :
    ((columnChunkPieces omitted chunks).map (Sum.map (List.map f) f)).flatMap
        (Sum.elim id List.singleton) =
      columnRunHeadsWithCuts (columnChunkCuts (chunks.map (Sum.map (List.map f) f))) none := by
  rw [mapped_pieces_flatten, columnChunkPieces_flatten, columnChunkCuts_heads,
    columnChunkCuts_heads, columnChunkRuns_map f chunks hinj]

omit [DecidableEq α] [DecidableEq β] in
theorem mapped_pieces_regular (f : α → β) (pieces : List (List α ⊕ α)) :
    (pieces.map (Sum.map (List.map f) f)).filterMap (Sum.elim some (fun _ => none)) =
      (pieces.filterMap (Sum.elim some (fun _ => none))).map (List.map f) := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
      cases piece <;> simp only [List.map_cons, Sum.map_inl, Sum.map_inr,
        List.filterMap_cons, Sum.elim_inl, Sum.elim_inr] <;> rw [ih]

omit [DecidableEq α] [DecidableEq β] in
theorem mapped_pieces_omitted (f : α → β) (pieces : List (List α ⊕ α)) :
    (pieces.map (Sum.map (List.map f) f)).filterMap (Sum.elim (fun _ => none) some) =
      (pieces.filterMap (Sum.elim (fun _ => none) some)).map f := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
      cases piece <;> simp only [List.map_cons, Sum.map_inl, Sum.map_inr,
        List.filterMap_cons, Sum.elim_inl, Sum.elim_inr] <;> rw [ih]

end TwoPointCorrelations

end OAI
