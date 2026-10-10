import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MergeOrdering

namespace OAI

/-!
# The executable tournament merge as a finite reader

Only the tournament and its row cursors are stored. The complete output list
is a proof view, defined by the remaining-occurrence potential. The reader
law connects this actual merge to the stopped joins and bounded dictionaries.
-/

namespace LowSpaceSubsetSum
namespace MergedReader

universe u v

variable {α : Type u} {σ : Type v} {d : ℕ}

structure State (key : α → ℤ) (view : σ → List α) (d : ℕ) where
  tree : Tournament.Tree (RowMerge.Front d α σ) d
  valid : Tournament.Valid (fun x => key x.value) tree
  aligned : RowMerge.Aligned tree
  sorted : RowMerge.RowsSorted key view tree

theorem advance_sorted (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (s : State key view d) {a : α} {t : Tournament.Tree (RowMerge.Front d α σ) d}
    (ha : RowMerge.advance key read s.tree = some (a, t)) :
    RowMerge.RowsSorted key view t := by
  cases hw : Tournament.winner s.tree with
  | none => simp [RowMerge.advance, hw] at ha
  | some x =>
    have heq : (x.value, Tournament.replace (fun y => key y.value) s.tree x.row
        (RowMerge.front read x.row x.after)) = (a, t) := by
      simpa [RowMerge.advance, hw] using ha
    rw [← (Prod.mk.inj heq).2]
    exact RowMerge.replacement_rowsSorted key read view hread s.tree
      s.valid s.aligned s.sorted hw

theorem advance_consumes_one (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (s : State key view d) {a : α} {t : Tournament.Tree (RowMerge.Front d α σ) d}
    (ha : RowMerge.advance key read s.tree = some (a, t)) :
    RowMerge.potential view t + 1 = RowMerge.potential view s.tree := by
  cases hw : Tournament.winner s.tree with
  | none => simp [RowMerge.advance, hw] at ha
  | some x =>
    have heq : (x.value, Tournament.replace (fun y => key y.value) s.tree x.row
        (RowMerge.front read x.row x.after)) = (a, t) := by
      simpa [RowMerge.advance, hw] using ha
    rw [← (Prod.mk.inj heq).2]
    exact RowMerge.replacement_consumes_one key read view hread s.tree
      s.valid s.aligned hw

def next (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (s : State key view d) : Option (α × State key view d) :=
  match ha : RowMerge.advance key read s.tree with
  | none => none
  | some (a, t) => some (a, ⟨t,
      RowMerge.advance_valid key read s.tree s.valid ha,
      RowMerge.advance_aligned key read s.tree s.aligned ha,
      advance_sorted key read view hread s ha⟩)

/-- The output view is never a field of the executable state. -/
def output (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (s : State key view d) : List α :=
  RowMerge.trace key read (RowMerge.potential view s.tree) s.tree

theorem next_none (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (s : State key view d) (ha : RowMerge.advance key read s.tree = none) :
    next key read view hread s = none := by
  unfold next
  split
  · rfl
  · rename_i a t ht
    rw [ha] at ht
    cases ht

theorem next_some (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (s : State key view d) {a : α} {t : Tournament.Tree (RowMerge.Front d α σ) d}
    (ha : RowMerge.advance key read s.tree = some (a, t)) :
    next key read view hread s = some (a, ⟨t,
      RowMerge.advance_valid key read s.tree s.valid ha,
      RowMerge.advance_aligned key read s.tree s.aligned ha,
      advance_sorted key read view hread s ha⟩) := by
  unfold next
  split
  · rename_i hn
    rw [ha] at hn
    cases hn
  · rename_i b t' ht
    have heq : (a, t) = (b, t') := Option.some.inj (ha.symm.trans ht)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    rfl

theorem reader (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : RowMerge.IsReader read view) :
    RowMerge.IsReader (next (d := d) key read view hread) (output key read view) := by
  intro s
  cases ha : RowMerge.advance key read s.tree with
  | none =>
    rw [next_none key read view hread s ha]
    unfold output
    cases hp : RowMerge.potential view s.tree with
    | zero => rfl
    | succ k => simp only [RowMerge.trace, ha]
  | some z =>
    obtain ⟨a, t⟩ := z
    rw [next_some key read view hread s ha]
    have hdec := advance_consumes_one key read view hread s ha
    simp only [output, ← hdec, RowMerge.trace, ha]

theorem output_bag (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (s : State key view d) :
    (output key read view s : Multiset α) = RowMerge.bag view s.tree :=
  RowMerge.trace_complete key read view hread _ s.tree s.valid s.aligned le_rfl

theorem output_length (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (s : State key view d) :
    (output key read view s).length = RowMerge.potential view s.tree := by
  have h := congrArg Multiset.card (output_bag key read view hread s)
  simpa only [Multiset.coe_card, RowMerge.bag_card] using h

theorem output_sorted (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (s : State key view d) :
    (output key read view s).Pairwise (fun x y => key x ≤ key y) :=
  RowMerge.trace_sorted key read view hread _ s.tree s.valid s.aligned s.sorted

def start (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (rows : RowMerge.Path d → σ)
    (hsort : ∀ p, (view (rows p)).Pairwise (fun x y => key x ≤ key y)) :
    State key view d :=
  ⟨RowMerge.start key read rows, RowMerge.start_valid key read rows,
    RowMerge.start_aligned key read rows, fun p => by
      rw [RowMerge.start_remaining key read view hread rows p]
      exact hsort p⟩

theorem start_output_bag (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (rows : RowMerge.Path d → σ)
    (hsort : ∀ p, (view (rows p)).Pairwise (fun x y => key x ≤ key y)) :
    (output key read view (start key read view hread rows hsort) : Multiset α) =
      ∑ p : RowMerge.Path d, (view (rows p) : Multiset α) := by
  rw [output_bag key read view hread]
  simp only [RowMerge.bag, start, RowMerge.start_remaining key read view hread]

theorem start_output_length (key : α → ℤ) (read : σ → Option (α × σ))
    (view : σ → List α) (hread : RowMerge.IsReader read view)
    (rows : RowMerge.Path d → σ)
    (hsort : ∀ p, (view (rows p)).Pairwise (fun x y => key x ≤ key y)) :
    (output key read view (start key read view hread rows hsort)).length =
      ∑ p : RowMerge.Path d, (view (rows p)).length := by
  rw [output_length key read view hread]
  simp only [RowMerge.potential, start, RowMerge.start_remaining key read view hread]

theorem nodes_exact (key : α → ℤ) (view : σ → List α) (s : State key view d) :
    Tournament.nodes s.tree + 1 = 2 ^ (d + 1) := Tournament.nodes_exact s.tree

def advanceComparisons (key : α → ℤ) (view : σ → List α) (s : State key view d) : ℕ :=
  match Tournament.winner s.tree with
  | none => 0
  | some x => Tournament.replaceComparisons s.tree x.row

theorem advanceComparisons_le (key : α → ℤ) (view : σ → List α) (s : State key view d) :
    advanceComparisons key view s ≤ d := by
  unfold advanceComparisons
  split
  · exact Nat.zero_le d
  · exact (Tournament.replaceComparisons_eq _ _).le

end MergedReader
end LowSpaceSubsetSum

end OAI
