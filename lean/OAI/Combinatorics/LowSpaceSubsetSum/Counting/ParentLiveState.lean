import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedParentCollector

namespace OAI

/-! # Payload bounds for every live stored parent state

These bounds use the intrinsic bounded-mask and safe-dictionary types. They
apply to intermediate callback states and reader snapshots, including after
the first overflowing insertion.
-/

namespace LowSpaceSubsetSum.ParentLiveState

variable {n : ℕ}

def reader {I : Instance n} {F : IndexedMask n} {P : ℤ} {mode : FilteredStream.Mode}
    {right : Array (LeafRecord n)} {d : ℕ} (s : CountedParentJoin.State I F P mode right d) : ℕ :=
  (12 * n + 32) * (Tournament.nodes s.tree + 1)

theorem reader_exact {I : Instance n} {F : IndexedMask n} {P : ℤ} {mode : FilteredStream.Mode}
    {right : Array (LeafRecord n)} {d : ℕ} (s : CountedParentJoin.State I F P mode right d) :
    reader s = (12 * n + 32) * 2 ^ (d + 1) := by
  simp only [reader, Tournament.nodes_exact]

def dictionary {I : Instance n} {C : ℕ} (r : StoredEntry.Dictionary I C) : ℕ :=
  (r.val.records.toList.map StoredEntry.cells).sum + r.val.records.size +
    3 * BinaryTrie.nodes r.val.keys.tree + 8

private theorem list_cells (xs : List (StoredEntry n)) :
    (xs.map StoredEntry.cells).sum ≤ (n + 2) * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h := x.cells_le
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

theorem dictionary_le {I : Instance n} {C : ℕ} (r : StoredEntry.Dictionary I C) :
    dictionary r ≤ (n + 3 + 3 * (WeightEncoding.entryWidth I + 1)) * (C + 1) + 8 := by
  obtain ⟨hs, ht⟩ := RecordedDictionary.storage r.property
  have hl := list_cells r.val.records.toList
  simp only [Array.length_toList] at hl
  have hm := Nat.mul_le_mul_left (n + 2) hs
  have hn := Nat.mul_le_mul_left 3 ht
  unfold dictionary
  nlinarith only [hl, hs, hm, hn]

theorem dictionary_scale (I : Instance n) (C : ℕ) (r : StoredEntry.Dictionary I C) :
    dictionary r ≤ 18 * inputScale I * (C + 1) + 8 := by
  have hw := (WeightEncoding.widths_le I).2
  have hnu : n + 1 ≤ inputScale I := by unfold inputScale; omega
  have hcoef : n + 3 + 3 * (WeightEncoding.entryWidth I + 1) ≤ 18 * inputScale I := by omega
  exact (dictionary_le r).trans (Nat.add_le_add_right (Nat.mul_le_mul_right (C + 1) hcoef) 8)

def sharedArrays (left right : Array (LeafRecord n)) : ℕ :=
  (3 * n + 4) * (left.size + right.size + 1)

theorem sharedArrays_le (left right : Array (LeafRecord n)) (C : ℕ)
    (hl : left.size ≤ C) (hr : right.size ≤ C) :
    sharedArrays left right ≤ (3 * n + 4) * (2 * C + 1) := by
  exact Nat.mul_le_mul_left _ (by omega)

def frame {I : Instance n} {F : IndexedMask n} {P t : ℤ} {C : ℕ}
    {right₁ right₂ : Array (LeafRecord n)} {d₁ d₂ : ℕ}
    (st : StreamJoin.State (CountedParentJoin.State I F P .direct right₁ d₁)
      (CountedParentJoin.State I F P (.complementary t) right₂ d₂)
      (StoredEntry.Dictionary I C)) : ℕ :=
  reader st.left + reader st.right + dictionary st.user + 12

theorem frame_le {I : Instance n} {F : IndexedMask n} {P t : ℤ} {C : ℕ}
    {right₁ right₂ : Array (LeafRecord n)} {d₁ d₂ : ℕ}
    (st : StreamJoin.State (CountedParentJoin.State I F P .direct right₁ d₁)
      (CountedParentJoin.State I F P (.complementary t) right₂ d₂)
      (StoredEntry.Dictionary I C)) :
    frame st ≤ (12 * n + 32) * (2 ^ (d₁ + 1) + 2 ^ (d₂ + 1)) +
      18 * inputScale I * (C + 1) + 20 := by
  have h := dictionary_scale I C st.user
  simp only [frame, reader_exact]
  nlinarith only [h]

end LowSpaceSubsetSum.ParentLiveState

end OAI
