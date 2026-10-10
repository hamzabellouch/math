import OAI.NumberTheory.TwoPoint.Walks.CanonicalColumnNames
import OAI.NumberTheory.TwoPoint.Walks.ColumnEncodingRealization

namespace OAI

/-! Occurrence representatives recover all equalities involving imperfect positions. -/

namespace TwoPointCorrelations

private theorem reference_filterMap_length {α β : Type*} (reference : α → β)
    (entries : List (α × Bool)) :
    (entries.filterMap (fun a => if a.2 then none else some (reference a.1))).length =
      (entries.filter (fun a => !a.2)).length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨a, flag⟩
      cases flag <;> simp [ih]

/-- Once the regular-path and omitted-run geometry is encoded, all remaining
positions use their proved canonical representatives; no reference lookup
or equality-pattern reconstruction hypothesis is needed. -/
theorem canonical_column_encoding {α : Type*} [DecidableEq α]
    {n N segments omitted imperfect : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (label : Fin n → α) (perfect : Finset (Fin n)) (name : Fin n → ℕ ⊕ ℕ)
    (pathCode : ForestPathData.Code N segments)
    (cuts : List (Option CanonicalColumnLabel × Bool))
    (hcuts : cuts.map Prod.fst = canonicalPerfectEntries label perfect name)
    (pieces : List (List CanonicalColumnLabel ⊕ CanonicalColumnLabel))
    (hpieces : pieces.length ≤ N)
    (regularTail : List (List CanonicalColumnLabel))
    (hregular : List.ofFn (fun i => (evenEntries (decodeForestPaths pathCode i)).map
      CanonicalColumnLabel.regular) =
        pieces.filterMap (Sum.elim some (fun _ => none)) ++ regularTail)
    (omittedNames : List (Fin N)) (homittedSize : omittedNames.length ≤ omitted)
    (homitted : pieces.filterMap (Sum.elim (fun _ => none) some) =
      omittedNames.map (fun j => CanonicalColumnLabel.omitted j.val))
    (hheads : pieces.flatMap (Sum.elim id List.singleton) = columnRunHeadsWithCuts cuts none)
    (hI : ((columnPositionEntries perfect).filter (fun a => !a.2)).length ≤ imperfect) :
    ∃ code : ColumnDecoderCode N segments omitted imperfect,
      (decodeColumnLabels code).take n = List.ofFn (canonicalColumnName label perfect name) := by
  let reference : Fin n → Fin N := fun i => Fin.castLE hn (columnRepresentative label perfect i)
  have h := column_encoding_realization (imperfect := imperfect) hN (canonicalColumnName label perfect name) pathCode
    (columnPositionEntries perfect) (by simpa [columnPositionEntries] using hn)
    cuts (hcuts.trans (marked_position_entries label perfect name).symm)
    pieces hpieces regularTail hregular omittedNames homittedSize homitted hheads reference
    (by rw [reference_filterMap_length]; exact hI)
    (by intro a _ _; simpa only [reference, columnPositionEntries, List.length_ofFn, Fin.val_castLE] using
      (columnRepresentative label perfect a.1).isLt)
    (by intro a _ _; rw [marked_position_entries]; exact canonical_reference_resolves label perfect name a.1)
  simpa only [columnPositionEntries, List.length_ofFn, List.map_ofFn, Function.comp_def] using h

end TwoPointCorrelations

end OAI
