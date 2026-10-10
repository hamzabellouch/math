import OAI.NumberTheory.TwoPoint.Bounds.BoundedColumnCodes

namespace OAI

/-! Pass from recovery of canonical names to the universal equality-pattern count. -/

namespace TwoPointCorrelations

noncomputable def decodeColumnPrefixPattern {n N S O I : ℕ} (hn : n ≤ N)
    (code : ColumnDecoderCode N S O I) : Fin n → Fin n → Bool :=
  fun i j => decodeColumnPattern code (Fin.castLE hn i) (Fin.castLE hn j)

theorem column_prefix_pattern_recovers {α : Type*} [DecidableEq α] {n N S O I : ℕ}
    (hn : n ≤ N) (code : ColumnDecoderCode N S O I)
    (label : Fin n → α) (names : Fin n → CanonicalColumnLabel)
    (hprefix : (decodeColumnLabels code).take n = List.ofFn names)
    (heq : ∀ i j, names i = names j ↔ label i = label j) :
    decodeColumnPrefixPattern hn code = fun i j => decide (label i = label j) := by
  have hlookup (i : Fin n) :
      (decodeColumnLabels code).getD i.val (.freshImperfect 0) = names i := by
    have h := congrArg (fun l => l.getD i.val (.freshImperfect 0)) hprefix
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt i.isLt,
      List.getElem?_ofFn, dite_eq_left i.isLt, Fin.eta, Option.getD_some] using h
  funext i j
  unfold decodeColumnPrefixPattern decodeColumnPattern
  simp only [Fin.val_castLE, hlookup]
  simp only [heq i j]

/-- Restricting to the original column positions does not enlarge the
coefficient-independent universe of patterns. -/
theorem card_column_prefix_patterns {n N S O I : ℕ} (hn : n ≤ N) :
    Nat.card (Set.range (@decodeColumnPrefixPattern n N S O I hn)) ≤
      2 ^ (6 * N + 1) * N ^ (2 * S + O + I) := by
  let f := @decodeColumnPrefixPattern n N S O I hn
  have h := Nat.card_le_card_of_surjective (fun code => (⟨f code, code, rfl⟩ : Set.range f))
    (by rintro ⟨_, code, rfl⟩; exact ⟨code, rfl⟩)
  exact h.trans (by simpa only [Nat.card_eq_fintype_card] using card_columnDecoderCode_le N S O I)

end TwoPointCorrelations

end OAI
