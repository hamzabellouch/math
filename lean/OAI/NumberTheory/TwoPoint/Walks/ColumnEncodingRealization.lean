import OAI.NumberTheory.TwoPoint.Walks.ColumnBoundaryEncoding
import OAI.NumberTheory.TwoPoint.Bounds.PaddedListCode

namespace OAI

/-! A full column code from path segments, omitted runs and occurrence references. -/

namespace TwoPointCorrelations

private def columnPieceMask (pieces : List (List CanonicalColumnLabel ⊕ CanonicalColumnLabel)) :
    List Bool := pieces.map (Sum.elim (fun _ => true) (fun _ => false))

private def columnPieceRegular (pieces : List (List CanonicalColumnLabel ⊕ CanonicalColumnLabel)) :
    List (List CanonicalColumnLabel) :=
  pieces.filterMap (Sum.elim some (fun _ => none))

private def columnPieceOmitted (pieces : List (List CanonicalColumnLabel ⊕ CanonicalColumnLabel)) :
    List CanonicalColumnLabel :=
  pieces.filterMap (Sum.elim (fun _ => none) some)

private def columnPieceFlatten (pieces : List (List CanonicalColumnLabel ⊕ CanonicalColumnLabel)) :
    List CanonicalColumnLabel :=
  pieces.flatMap (Sum.elim id List.singleton)

theorem resolveColumnReference_append (full padding : List (Option CanonicalColumnLabel))
    (j : ℕ) (hj : j < full.length) :
    resolveColumnReference (full ++ padding) j = resolveColumnReference full j := by
  simp only [resolveColumnReference, List.getElem?_append_left hj]

/-- The geometric inputs are exact regular path lists and an interleaving
of regular segments with omitted runs. No full equality-pattern or decoder
conclusion is assumed. All unused slots may be padded independently. -/
theorem column_encoding_realization {α : Type*} {N segments omitted imperfect : ℕ} (hN : 0 < N)
    (name : α → CanonicalColumnLabel)
    (pathCode : ForestPathData.Code N segments)
    (entries : List (α × Bool)) (hentries : entries.length ≤ N)
    (cuts : List (Option CanonicalColumnLabel × Bool))
    (hcuts : cuts.map Prod.fst = markedColumn name entries)
    (pieces : List (List CanonicalColumnLabel ⊕ CanonicalColumnLabel))
    (hpieces : pieces.length ≤ N)
    (regularTail : List (List CanonicalColumnLabel))
    (hregular : List.ofFn (fun i => (evenEntries (decodeForestPaths pathCode i)).map CanonicalColumnLabel.regular) =
      columnPieceRegular pieces ++ regularTail)
    (omittedNames : List (Fin N)) (homittedSize : omittedNames.length ≤ omitted)
    (homitted : columnPieceOmitted pieces =
      omittedNames.map (fun j => CanonicalColumnLabel.omitted j.val))
    (hheads : columnPieceFlatten pieces = columnRunHeadsWithCuts cuts none)
    (reference : α → Fin N)
    (hreferenceSize :
      (entries.filterMap (fun a => if a.2 then none else some (reference a.1))).length ≤ imperfect)
    (hreferenceBound : ∀ a ∈ entries, a.2 = false → (reference a.1).val < entries.length)
    (hreference : ∀ a ∈ entries, a.2 = false →
      resolveColumnReference (markedColumn name entries) (reference a.1).val = name a.1) :
    ∃ code : ColumnDecoderCode N segments omitted imperfect,
      (decodeColumnLabels code).take entries.length = entries.map (fun a => name a.1) := by
  let zero : Fin N := ⟨0, hN⟩
  let marked := markedColumn name entries
  let flags := columnFlagsWithCuts cuts none
  have hflags : flags.length ≤ N := by
    have hc := congrArg List.length hcuts
    simp only [List.length_map, markedColumn] at hc
    simpa only [flags, columnFlagsWithCuts_length] using hc.le.trans hentries
  have hmask : (columnPieceMask pieces).length ≤ N := by
    simpa only [columnPieceMask, List.length_map] using hpieces
  let refs := entries.filterMap (fun a => if a.2 then none else some (reference a.1))
  let code : ColumnDecoderCode N segments omitted imperfect :=
    (pathCode, paddedListCode (columnPieceMask pieces) hmask false,
      paddedListCode flags hflags (false, false),
      paddedListCode omittedNames homittedSize zero,
      paddedListCode refs hreferenceSize zero)
  let omittedTail := (List.replicate (omitted - omittedNames.length) zero).map
    (fun j => CanonicalColumnLabel.omitted j.val)
  let maskPadding := List.replicate (N - (columnPieceMask pieces).length) false
  let extraRuns := mergeColumnRuns maskPadding regularTail omittedTail
  have hpaths : List.ofFn (fun i => (evenEntries (decodeForestPaths code.1 i)).map
      CanonicalColumnLabel.regular) = columnPieceRegular pieces ++ regularTail := by
    change List.ofFn (fun i => (evenEntries (decodeForestPaths pathCode i)).map
      CanonicalColumnLabel.regular) = _
    exact hregular
  have homit : List.ofFn (fun i => CanonicalColumnLabel.omitted (code.2.2.2.1 i).val) =
      columnPieceOmitted pieces ++ omittedTail := by
    change List.ofFn (fun i => CanonicalColumnLabel.omitted
      (paddedListCode omittedNames homittedSize zero i).val) = _
    rw [List.ofFn_comp' (paddedListCode omittedNames homittedSize zero)
      (fun j : Fin N => CanonicalColumnLabel.omitted j.val),
      paddedListCode_ofFn, List.map_append, ← homitted]
  have hruns : mergeColumnRuns (List.ofFn code.2.1)
      (List.ofFn (fun i => (evenEntries (decodeForestPaths code.1 i)).map CanonicalColumnLabel.regular))
      (List.ofFn (fun i => CanonicalColumnLabel.omitted (code.2.2.2.1 i).val)) =
        columnRunHeadsWithCuts cuts none ++ extraRuns := by
    rw [hpaths, homit]
    change mergeColumnRuns (List.ofFn (paddedListCode (columnPieceMask pieces) hmask false)) _ _ = _
    rw [paddedListCode_ofFn]
    have hm := mergeColumnRuns_append pieces maskPadding regularTail omittedTail
    have hm' : mergeColumnRuns (columnPieceMask pieces ++ maskPadding)
        (columnPieceRegular pieces ++ regularTail) (columnPieceOmitted pieces ++ omittedTail) =
        columnPieceFlatten pieces ++ extraRuns := by
      simpa only [columnPieceMask, columnPieceRegular, columnPieceOmitted,
        columnPieceFlatten, extraRuns] using hm
    rw [hheads] at hm'
    exact hm'
  let full := expandColumnRuns (List.ofFn code.2.2.1) (columnRunHeadsWithCuts cuts none ++ extraRuns) none
  have hfullPrefix : full.take entries.length = marked := by
    have ht := expandColumnRuns_take_append flags (List.replicate (N - flags.length) (false, false))
      (columnRunHeadsWithCuts cuts none ++ extraRuns) none
    rw [expandColumnRuns_cuts_recover] at ht
    rw [hcuts] at ht
    change (expandColumnRuns (List.ofFn (paddedListCode flags hflags (false, false)))
      (columnRunHeadsWithCuts cuts none ++ extraRuns) none).take entries.length = marked
    rw [paddedListCode_ofFn]
    have hc : cuts.length = entries.length := by
      have hh := congrArg List.length hcuts
      simpa only [List.length_map, markedColumn] using hh
    simpa only [flags, columnFlagsWithCuts_length, hc, marked] using ht
  have hfull : full = marked ++ full.drop entries.length := by
    rw [← hfullPrefix]
    exact (List.take_append_drop _ _).symm
  have hlookup : ∀ a ∈ entries, a.2 = false →
      resolveColumnReference full (reference a.1).val = name a.1 := by
    intro a ha hp
    rw [hfull, resolveColumnReference_append]
    · exact hreference a ha hp
    · simpa only [marked, markedColumn, List.length_map] using hreferenceBound a ha hp
  have hrefs : List.ofFn (fun i => (code.2.2.2.2 i).val) =
      imperfectColumnReferences (fun a => (reference a).val) entries ++
        (List.replicate (imperfect - refs.length) zero).map Fin.val := by
    change List.ofFn (fun i => (paddedListCode refs hreferenceSize zero i).val) = _
    rw [List.ofFn_comp', paddedListCode_ofFn, List.map_append]
    congr 1
    simp only [refs, imperfectColumnReferences, List.map_filterMap]
    apply List.filterMap_congr
    intro a _
    cases a.2 <;> rfl
  have hatt := attachImperfectLabels_recover_append full name (fun a => (reference a).val)
    entries (full.drop entries.length)
    ((List.replicate (imperfect - refs.length) zero).map Fin.val) hlookup
  refine ⟨code, ?_⟩
  have hdecode : decodeColumnLabels code =
      entries.map (fun a => name a.1) ++ attachImperfectLabels full (full.drop entries.length)
        ((List.replicate (imperfect - refs.length) zero).map Fin.val) := by
    dsimp only [decodeColumnLabels]
    rw [hruns]
    change attachImperfectLabels full full (List.ofFn (fun i => (code.2.2.2.2 i).val)) = _
    rw [hrefs]
    calc
      _ = attachImperfectLabels full (marked ++ full.drop entries.length)
          (imperfectColumnReferences (fun a => (reference a).val) entries ++
            (List.replicate (imperfect - refs.length) zero).map Fin.val) :=
        congrArg (fun l => attachImperfectLabels full l _) hfull
      _ = _ := hatt
  rw [hdecode]
  simpa only [List.length_map] using
    (List.take_left (l₁ := entries.map (fun a => name a.1))
      (l₂ := attachImperfectLabels full (full.drop entries.length)
        ((List.replicate (imperfect - refs.length) zero).map Fin.val)))

end TwoPointCorrelations

end OAI
