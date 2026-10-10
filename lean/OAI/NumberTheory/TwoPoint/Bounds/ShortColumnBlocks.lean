import OAI.NumberTheory.TwoPoint.Bounds.PerfectIntervalFamily
import OAI.NumberTheory.TwoPoint.Walks.ColumnPieceMembership
import OAI.NumberTheory.TwoPoint.Walks.CanonicalColumnNames

namespace OAI

/-! The actual short perfect blocks of a finite column, with all positions and budgets. -/

namespace TwoPointCorrelations

variable {α : Type*} {n : ℕ}

def columnNatLabel (label : Fin n → α) (hn : 0 < n) (t : ℕ) : α :=
  if ht : t < n then label ⟨t, ht⟩ else label ⟨0, hn⟩

def columnNatPerfect (perfect : Finset (Fin n)) (t : ℕ) : Bool :=
  if ht : t < n then decide ((⟨t, ht⟩ : Fin n) ∈ perfect) else false

theorem columnNatLabel_fin (label : Fin n → α) (hn : 0 < n) (i : Fin n) :
    columnNatLabel label hn i.val = label i := by
  simp only [columnNatLabel, dite_eq_left i.isLt, Fin.eta]

theorem columnNatPerfect_fin (perfect : Finset (Fin n)) (i : Fin n) :
    columnNatPerfect perfect i.val = decide (i ∈ perfect) := by
  simp [columnNatPerfect, i.isLt]

theorem range_map_eq_ofFn {β : Type*} (f : ℕ → β) (n : ℕ) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  simpa using (List.ofFn_getElem_eq_map (List.range n) f).symm

def shortColumnChunks (label : Fin n → α) (hn : 0 < n) (perfect : Finset (Fin n)) (s : ℕ) :
    List (List α ⊕ α) :=
  (shortPerfectColumnChunks s ((List.range n).map (fun t => (t, columnNatPerfect perfect t)))).map
    (Sum.map (List.map (columnNatLabel label hn)) (columnNatLabel label hn))

theorem shortColumnChunks_entries (label : Fin n → α) (hn : 0 < n)
    (perfect : Finset (Fin n)) (s : ℕ) :
    columnChunkEntries (shortColumnChunks label hn perfect s) =
      (columnPositionEntries perfect).map (fun p => (label p.1, p.2)) := by
  rw [shortColumnChunks, columnChunkEntries_map, shortPerfectColumnChunks_entries]
  simp only [Function.comp_def, range_map_eq_ofFn, columnNatLabel_fin,
    columnNatPerfect_fin, columnPositionEntries, List.map_ofFn]

/-- The short blocks used by the decoder are actual intervals, all of
length at most `s`. Their count and total length satisfy the original
position budgets, before any quotient geometry is used. -/
theorem shortColumnChunks_blocks (label : Fin n → α) (hn : 0 < n)
    (perfect : Finset (Fin n)) (s : ℕ) (hs : 0 < s) :
    ∃ blocks : List (ℕ × ℕ),
      (shortColumnChunks label hn perfect s).filterMap (Sum.elim some (fun _ => none)) =
        blocks.map (fun b => blockLabelList (columnNatLabel label hn) b.1 b.2) ∧
      (blocks.map Prod.snd).sum ≤ n ∧
      blocks.length ≤ n / s + ((columnPositionEntries perfect).filter (fun p => !p.2)).length + 1 ∧
      ∀ b ∈ blocks, b.1 + b.2 ≤ n ∧ b.2 ≤ s ∧
        ∀ t ∈ intervalPositions b, columnNatPerfect perfect t = true := by
  let entries := (List.range n).map (fun t => (t, columnNatPerfect perfect t))
  let chunks := shortPerfectColumnChunks s entries
  obtain ⟨blocks, hblocks, hcount, hsum, hvalid⟩ :=
    shortPerfectColumnChunks_interval_family n s (columnNatPerfect perfect)
  refine ⟨blocks, ?_, hsum, ?_, ?_⟩
  · change (chunks.map (Sum.map (List.map (columnNatLabel label hn)) (columnNatLabel label hn))).filterMap _ = _
    rw [mapped_pieces_regular, ← hblocks, List.map_map]
    simp only [intervalPositions, blockLabelList, List.map_map, Function.comp_def]
  · have hc := shortPerfectColumnChunks_count s entries
    rw [← hcount] at hc
    have hflags : (entries.filter (fun p => !p.2)).length =
        ((columnPositionEntries perfect).filter (fun p => !p.2)).length := by
      have he : entries = (columnPositionEntries perfect).map (fun p => (p.1.val, p.2)) := by
        simp only [entries, range_map_eq_ofFn, columnNatPerfect_fin, columnPositionEntries, List.map_ofFn, Function.comp_def]
      rw [he, List.filter_map, List.length_map]
      rfl
    have he : entries.length = n := by simp only [entries, List.length_map, List.length_range]
    simpa only [he, hflags] using hc
  · intro b hb
    refine ⟨(hvalid b hb).1, ?_, (hvalid b hb).2⟩
    have hm : intervalPositions b ∈ chunks.filterMap (Sum.elim some (fun _ => none)) := by
      rw [← hblocks]
      exact List.mem_map.mpr ⟨b, hb, rfl⟩
    obtain ⟨piece, hp, he⟩ := List.mem_filterMap.mp hm
    have hi : Sum.inl (intervalPositions b) ∈ chunks := by
      cases piece with
      | inl block => cases he; exact hp
      | inr a => simp at he
    have hl := shortPerfectColumnChunks_regular_size s hs entries (intervalPositions b) hi
    simpa only [intervalPositions, List.length_map, List.length_range] using hl

end TwoPointCorrelations

end OAI
