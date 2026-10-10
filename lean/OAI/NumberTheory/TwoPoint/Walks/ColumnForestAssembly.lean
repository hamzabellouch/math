import OAI.NumberTheory.TwoPoint.Bounds.RegularFamilyNames
import OAI.NumberTheory.TwoPoint.Walks.ColumnPieceMembership
import OAI.NumberTheory.TwoPoint.Walks.CanonicalColumnEncoding
import OAI.NumberTheory.TwoPoint.Walks.ColumnPatternRecovery

namespace OAI

/-! Assemble an actual column code from the shared forest of its regular paths. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]

theorem column_code_from_regular_forest {n N O I : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (label : Fin n → α) (perfect : Finset (Fin n))
    (regular : Finset α) (number : regular → ℕ) (lineNumber : α → ℕ)
    (hnumber : ∀ z (hz : z ∈ regular), lineNumber z = number ⟨z, hz⟩)
    (labelNat : ℕ → α)
    (chunks : List (List α ⊕ α)) (blocks : List (ℕ × ℕ))
    (hentries : columnChunkEntries chunks =
      (columnPositionEntries perfect).map (fun p => (label p.1, p.2)))
    (hblocks : chunks.filterMap (Sum.elim some (fun _ => none)) =
      blocks.map (fun b => blockLabelList labelNat b.1 b.2))
    (pathCode : ForestPathData.Code N
      (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).length)
    (hbound : ∀ segment ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
      ∀ p ∈ segment, lineNumber p.2 < N)
    (hinj : ∀ segment ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
      ∀ p ∈ segment,
      ∀ other ∈ indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks,
      ∀ q ∈ other, lineNumber p.2 = lineNumber q.2 → p.2 = q.2)
    (hdecode : List.ofFn (fun i => evenEntries (decodeForestPaths pathCode i)) =
      (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).map
        (fun segment => segment.map (fun p => lineNumber p.2)))
    (hO : omittedPieceCount (columnChunkPieces (fun z => decide (z ∉ regular)) chunks) ≤ O)
    (hI : ((columnPositionEntries perfect).filter (fun a => !a.2)).length ≤ I) :
    ∃ code : ColumnDecoderCode N
        (indexedRegularSegments labelNat (fun z => decide (z ∉ regular)) blocks).length O I,
      (decodeColumnLabels code).take n =
        List.ofFn (canonicalColumnName label perfect (forestPerfectName label perfect regular number)) ∧
      decodeColumnPrefixPattern hn code = (fun i j => decide (label i = label j)) := by
  let isOmitted := fun z : α => decide (z ∉ regular)
  let segments := indexedRegularSegments labelNat isOmitted blocks
  let names := forestPerfectName label perfect regular number
  let f := observedColumnName label perfect names
  let raw := columnChunkPieces isOmitted chunks
  let pieces := raw.map (Sum.map (List.map f) f)
  let namedChunks := chunks.map (Sum.map (List.map f) f)
  let cuts := columnChunkCuts namedChunks
  have hprops := regular_family_name_properties label perfect regular number lineNumber hnumber
    labelNat chunks blocks hentries hblocks hbound hinj
  have heq (i j : Fin n) : f (label i) = f (label j) ↔ label i = label j :=
    observed_forest_name_eq_iff label perfect regular number hprops.2 i j
  have hlocal : ∀ block, Sum.inl block ∈ chunks →
      ∀ a ∈ block, ∀ b ∈ block, f a = f b ↔ a = b := by
    intro block hb a ha b hbb
    have ha' : (a, true) ∈ columnChunkEntries chunks :=
      List.mem_flatMap.mpr ⟨.inl block, hb, List.mem_map.mpr ⟨a, ha, rfl⟩⟩
    have hb' : (b, true) ∈ columnChunkEntries chunks :=
      List.mem_flatMap.mpr ⟨.inl block, hb, List.mem_map.mpr ⟨b, hbb, rfl⟩⟩
    obtain ⟨i, _, hi⟩ := perfect_label_position label perfect chunks hentries a ha'
    obtain ⟨j, _, hj⟩ := perfect_label_position label perfect chunks hentries b hb'
    simpa only [hi, hj] using heq i j
  have hcuts : cuts.map Prod.fst = canonicalPerfectEntries label perfect names := by
    change (columnChunkCuts namedChunks).map Prod.fst = _
    rw [columnChunkCuts_values]
    change (columnChunkEntries (chunks.map (Sum.map (List.map f) f))).map _ = _
    rw [columnChunkEntries_map, hentries]
    simp only [columnPositionEntries, List.map_ofFn, canonicalPerfectEntries,
      Function.comp_def]
    congr 1
    funext i
    by_cases hi : i ∈ perfect <;> simp [f, observedColumnName_at, hi]
  have hpieces : pieces.length ≤ N := by
    change (raw.map _).length ≤ N
    rw [List.length_map]
    apply (columnChunkPieces_length_le isOmitted chunks).trans
    rw [hentries, List.length_map]
    simpa only [columnPositionEntries, List.length_ofFn] using hn
  have hlabels : segments.map (List.map Prod.snd) =
      raw.filterMap (Sum.elim some (fun _ => none)) :=
    indexedRegularSegments_eq_regular_pieces labelNat isOmitted chunks blocks hblocks
  have hregularName : ∀ segment ∈ segments, ∀ p ∈ segment,
      f p.2 = .regular (lineNumber p.2) := by
    intro segment hs p hp
    have hs' : segment.map Prod.snd ∈ raw.filterMap (Sum.elim some (fun _ => none)) := by
      rw [← hlabels]
      exact List.mem_map.mpr ⟨segment, hs, rfl⟩
    obtain ⟨piece, hpiece, hs'⟩ := List.mem_filterMap.mp hs'
    have hinl : Sum.inl (segment.map Prod.snd) ∈ raw := by
      cases piece with
      | inl l => cases hs'; exact hpiece
      | inr a => simp at hs'
    have hm := (columnChunkPieces_regular_membership isOmitted chunks _ hinl).2 p.2
      (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hr : p.2 ∈ regular := by simpa only [isOmitted, decide_eq_false_iff_not, not_not] using hm.1
    obtain ⟨i, hip, hi⟩ := perfect_label_position label perfect chunks hentries p.2 hm.2
    have hir : label i ∈ regular := hi.symm ▸ hr
    have hn' : lineNumber p.2 = number ⟨label i, hir⟩ := by
      rw [← hi]
      exact hnumber (label i) hir
    calc
      f p.2 = f (label i) := congrArg f hi.symm
      _ = .regular (number ⟨label i, hir⟩) := observed_forest_name_regular label perfect regular number i hip hir
      _ = _ := congrArg CanonicalColumnLabel.regular hn'.symm
  have hregular : List.ofFn (fun i => (evenEntries (decodeForestPaths pathCode i)).map
      CanonicalColumnLabel.regular) = pieces.filterMap (Sum.elim some (fun _ => none)) := by
    have hd := congrArg (List.map (List.map CanonicalColumnLabel.regular)) hdecode
    simp only [List.map_ofFn, List.map_map, Function.comp_def] at hd
    calc
      _ = segments.map (fun segment => segment.map (fun p => .regular (lineNumber p.2))) := hd
      _ = segments.map (fun segment => segment.map (fun p => f p.2)) := by
        apply List.map_congr_left
        intro segment hs
        apply List.map_congr_left
        intro p hp
        exact (hregularName segment hs p hp).symm
      _ = (segments.map (List.map Prod.snd)).map (List.map f) := by
        simp only [List.map_map, Function.comp_def]
      _ = (raw.filterMap (Sum.elim some (fun _ => none))).map (List.map f) := by rw [hlabels]
      _ = _ := (mapped_pieces_regular f raw).symm
  have homit : ∀ a ∈ pieces.filterMap (Sum.elim (fun _ => none) some),
      ∃ j : Fin N, a = .omitted j.val := by
    intro a ha
    change a ∈ (raw.map (Sum.map (List.map f) f)).filterMap _ at ha
    rw [mapped_pieces_omitted] at ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    obtain ⟨piece, hp, hz⟩ := List.mem_filterMap.mp hz
    have hinr : Sum.inr z ∈ raw := by
      cases piece with
      | inl l => simp at hz
      | inr b => cases hz; exact hp
    have hm := columnChunkPieces_omitted_membership isOmitted chunks z hinr
    have hr : z ∉ regular := of_decide_eq_true hm.1
    obtain ⟨i, hip, hi⟩ := perfect_label_position label perfect chunks hentries z hm.2
    have hir : label i ∉ regular := hi.symm ▸ hr
    refine ⟨Fin.castLE hn (columnRepresentative label perfect i), ?_⟩
    simpa only [f, names, hi, Fin.val_castLE] using
      observed_forest_name_omitted label perfect regular number i hip hir
  obtain ⟨omittedNames, holen, homap⟩ := omitted_names_lift _ homit
  have ho : omittedNames.length ≤ O := by
    rw [holen]
    change ((raw.map (Sum.map (List.map f) f)).filterMap _).length ≤ O
    rw [mapped_pieces_omitted, List.length_map]
    exact hO
  have hheads : pieces.flatMap (Sum.elim id List.singleton) = columnRunHeadsWithCuts cuts none :=
    mapped_column_pieces_heads f isOmitted chunks hlocal
  obtain ⟨code, hprefix⟩ := canonical_column_encoding hN hn label perfect names pathCode cuts hcuts pieces hpieces []
    (by simpa only [List.append_nil] using hregular) omittedNames ho homap.symm hheads hI
  exact ⟨code, hprefix, column_prefix_pattern_recovers hn code label _ hprefix
    (canonical_forest_name_eq_iff label perfect regular number hprops.2)⟩

end TwoPointCorrelations

end OAI
