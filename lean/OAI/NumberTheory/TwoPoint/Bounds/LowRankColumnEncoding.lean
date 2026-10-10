import OAI.NumberTheory.TwoPoint.Walks.ColumnGeometryEncoding
import OAI.NumberTheory.TwoPoint.Bounds.ShortColumnBlocks
import OAI.NumberTheory.TwoPoint.Bounds.RegularLineAnchors
import OAI.NumberTheory.TwoPoint.Walks.ColumnBudget

namespace OAI

/-! Low-rank lit departures give a full code for the actual short-block column. -/

namespace TwoPointCorrelations

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

def imperfectColumnCount (perfect : Finset (Fin n)) : ℕ :=
  ((columnPositionEntries perfect).filter (fun p => !p.2)).length

theorem imperfectColumnCount_le (perfect : Finset (Fin n)) :
    imperfectColumnCount perfect ≤ n := by
  exact (List.length_filter_le _ _).trans (by simp [columnPositionEntries])

/-- The geometric conclusions required on every actual short perfect block. -/
def ShortColumnGeometry (label : Fin n → α) (hn : 0 < n)
    (coefficient : ℕ → ℝ) (perfect : Finset (Fin n)) (s : ℕ) : Prop :=
  ∀ start len, start + len ≤ n → len ≤ s →
      (∀ t ∈ intervalPositions (start, len), columnNatPerfect perfect t = true) →
      (∀ i j k : Fin (blockLabelList (columnNatLabel label hn) start len).length,
        i ≤ j → j ≤ k →
        (blockLabelList (columnNatLabel label hn) start len).get i =
          (blockLabelList (columnNatLabel label hn) start len).get k →
        (blockLabelList (columnNatLabel label hn) start len).get j =
          (blockLabelList (columnNatLabel label hn) start len).get i) ∧
      (∀ a b z, start ≤ a → a < b → b ≤ start + len →
        (∀ t ∈ Ico a b, columnNatLabel label hn t = z) →
        (∑ t ∈ Ico a b, coefficient t) ≠ 0)

/-- Only actual lit departures enter the low-rank premise. The short
blocks and their complete decoder are constructed, not supplied as data. -/
theorem low_rank_short_column_code (label : Fin n → α) (hn : 0 < n)
    (coefficient : ℕ → ℝ) (perfect : Finset (Fin n)) (s r : ℕ) (hs : 0 < s)
    (hno : ∀ S : Finset (EqualLabelPairs (fun i : perfect => label i.val)), S.card = r →
      ¬LinearIndependent ℝ (pairFamily (labelPairVectors (fun i : perfect => label i.val)
        (fun i => formalDeparture (columnNatLabel label hn) coefficient i.val.val)) S))
    (hgeometry : ShortColumnGeometry label hn coefficient perfect s) :
    ∃ omittedLabels blocks segments omittedRuns : ℕ,
      omittedLabels < 2 * r ∧
      blocks ≤ n / s + imperfectColumnCount perfect + 1 ∧
      segments ≤ (omittedLabels + 1) * blocks ∧
      omittedRuns ≤ omittedLabels * blocks ∧
      segments ≤ n ∧ omittedRuns ≤ n ∧
      ∃ code : ColumnDecoderCode (2 * n) segments omittedRuns (imperfectColumnCount perfect),
        decodeColumnPrefixPattern (show n ≤ 2 * n by omega) code =
          fun i j => decide (label i = label j) := by
  classical
  let labelNat := columnNatLabel label hn
  let chunks := shortColumnChunks label hn perfect s
  obtain ⟨blocks, hblocks, hsum, hcount, hvalid⟩ := shortColumnChunks_blocks label hn perfect s hs
  obtain ⟨D, regular, anchor, hsmall, hind, hline⟩ :=
    exists_regular_line_anchors (fun i : perfect => label i.val)
      (fun i => formalDeparture labelNat coefficient i.val.val) r hno
  have hl : ∀ b ∈ blocks, ∀ t ∈ Ico b.1 (b.1 + b.2), ∀ ht : labelNat t ∈ regular,
      ∃ c : ℝ, D.mkQ (formalDeparture labelNat coefficient t) =
        anchor ⟨labelNat t, ht⟩ + c • D.mkQ (Pi.basisFun ℝ α (labelNat t)) := by
    intro b hb t ht hr
    obtain ⟨htlo, hthi⟩ := mem_Ico.mp ht
    have htn : t < n := (mem_Ico.mp ht).2.trans_le (hvalid b hb).1
    have htp : columnNatPerfect perfect t = true := (hvalid b hb).2.2 t (by
      simp only [intervalPositions, List.mem_map, List.mem_range]
      exact ⟨t - b.1, by omega, by omega⟩)
    have hip : (⟨t, htn⟩ : Fin n) ∈ perfect := by
      simpa only [columnNatPerfect, dite_eq_left htn, decide_eq_true_eq] using htp
    exact hline ⟨labelNat t, hr⟩ ⟨⟨t, htn⟩, hip⟩ (by
      change label ⟨t, htn⟩ = columnNatLabel label hn t
      simp only [columnNatLabel, dite_eq_left htn])
  have hg (b) (hb : b ∈ blocks) := hgeometry b.1 b.2
    (hvalid b hb).1 (hvalid b hb).2.1 (hvalid b hb).2.2
  have hi : ∀ l, Sum.inl l ∈ chunks → ∀ i j k : Fin l.length,
      i ≤ j → j ≤ k → l.get i = l.get k → l.get j = l.get i := by
    intro l hl
    have hm : l ∈ chunks.filterMap (Sum.elim some (fun _ => none)) :=
      List.mem_filterMap.mpr ⟨.inl l, hl, rfl⟩
    rw [hblocks] at hm
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
    exact (hg b hb).1
  have ho := columnChunk_piece_budgets chunks regularᶜ hi
  let pieces := columnChunkPieces (fun z => decide (z ∉ regular)) chunks
  let S := (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).length
  let O := omittedPieceCount pieces
  have hp : (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).map
      (List.map Prod.snd) = pieces.filterMap (Sum.elim some (fun _ => none)) :=
    indexedRegularSegments_eq_regular_pieces labelNat _ chunks blocks hblocks
  have hS : S = regularPieceCount pieces := by
    have he := congrArg List.length hp
    simpa only [List.length_map, regularPieceCount] using he
  have hB : perfectChunkCount chunks = blocks.length := by
    change (chunks.filterMap (Sum.elim some (fun _ => none))).length = blocks.length
    change (shortColumnChunks label hn perfect s |>.filterMap (Sum.elim some (fun _ => none))).length = _
    rw [hblocks, List.length_map]
  have hO : O ≤ regularᶜ.card * blocks.length := by
    simpa only [pieces, mem_compl, hB] using ho.1
  have hSbound : S ≤ (regularᶜ.card + 1) * blocks.length := by
    rw [hS]
    simpa only [pieces, mem_compl, hB] using ho.2
  have hentries := shortColumnChunks_entries label hn perfect s
  have hpieces : pieces.length ≤ n := (columnChunkPieces_length_le _ chunks).trans (by
    rw [hentries]
    simp only [List.length_map, columnPositionEntries, List.length_ofFn]
    exact le_rfl)
  have hSn : S ≤ n := by
    rw [hS]
    exact (List.length_filterMap_le _ _).trans hpieces
  have hOn : O ≤ n := (List.length_filterMap_le _ _).trans hpieces
  obtain ⟨code, hcode⟩ := column_code_from_quotient_geometry (by omega : 0 < 2 * n)
    (by omega : n ≤ 2 * n) label perfect regular labelNat coefficient chunks blocks hentries hblocks
    D anchor hind hl (fun b hb => (hg b hb).2) (Nat.mul_le_mul_left 2 hsum) le_rfl le_rfl
  exact ⟨regularᶜ.card, blocks.length, S, O, hsmall, hcount, hSbound, hO, hSn, hOn, code, hcode⟩

end TwoPointCorrelations

end OAI
