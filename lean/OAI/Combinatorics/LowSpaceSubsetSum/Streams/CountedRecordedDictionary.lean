import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedTrie

namespace OAI

/-! # Recorded dictionary feed using its cached array length

The record array's length is the exact number of distinct keys. The runtime
capacity comparison uses this scalar rather than traversing the trie. Key
encoding and the emitter are charged by their callers.
-/

namespace LowSpaceSubsetSum.CountedTrie

universe u
variable {α : Type u}

def recordedFeed (C : ℕ) (encode : α → List Bool) (x : α)
    (r : RecordedDictionary.State α) : RecordedDictionary.State α × ℕ :=
  let out := feed C (encode x) ⟨r.keys, r.records.size⟩
  (⟨out.1.state, if r.records.size < out.1.count then r.records.push x else r.records⟩,
    out.2 + 3)

theorem recordedFeed_work (C : ℕ) (encode : α → List Bool) (x : α)
    (r : RecordedDictionary.State α) :
    (recordedFeed C encode x r).2 ≤ 2 * (encode x).length + 11 := by
  exact Nat.add_le_add_right (feed_work C (encode x) ⟨r.keys, r.records.size⟩) 3

theorem recordedFeed_value {C width : ℕ} {encode : α → List Bool}
    (x : α) (r : RecordedDictionary.State α)
    (hr : RecordedDictionary.Invariant C width encode r) (hx : (encode x).length = width) :
    (recordedFeed C encode x r).1 = RecordedDictionary.feed C encode x r := by
  by_cases ho : r.keys.overflow = true
  · simp [recordedFeed, feed, ho, RecordedDictionary.feed, BinaryTrie.feed]
  · have hf : r.keys.overflow = false := Bool.eq_false_iff.mpr ho
    by_cases hd : BinaryTrie.contains r.keys.tree (encode x) = true
    · simp [recordedFeed, feed, contains_value, hf, hd, RecordedDictionary.feed, BinaryTrie.feed]
    · have hn : BinaryTrie.contains r.keys.tree (encode x) = false := Bool.eq_false_iff.mpr hd
      have he := BinaryTrie.entries_insert hr.safe.hasWidth hx
      simp only [hn, Bool.false_eq_true, ↓reduceIte] at he
      simp only [recordedFeed, feed, contains_value, insert_value, hf, hn,
        Bool.false_eq_true, ↓reduceIte, Nat.lt_succ_self, RecordedDictionary.feed,
        BinaryTrie.feed, Bool.false_or, he, ← hr.size_eq]

def recordedFold (C : ℕ) (encode : α → List Bool) :
    List α → RecordedDictionary.State α → RecordedDictionary.State α × ℕ
  | [], r => (r, 0)
  | x :: xs, r =>
    let first := recordedFeed C encode x r
    let rest := recordedFold C encode xs first.1
    (rest.1, first.2 + rest.2)

theorem recordedFold_value {C width : ℕ} {encode : α → List Bool}
    (xs : List α) (r : RecordedDictionary.State α)
    (hr : RecordedDictionary.Invariant C width encode r)
    (hw : ∀ x ∈ xs, (encode x).length = width) :
    (recordedFold C encode xs r).1 = xs.foldl (fun r x => RecordedDictionary.feed C encode x r) r := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih =>
    have hx := hw x (by simp)
    simp only [recordedFold, recordedFeed_value x r hr hx, List.foldl_cons]
    exact ih _ (RecordedDictionary.feed_invariant hr x hx) (fun y hy => hw y (by simp [hy]))

theorem recordedFold_work (C width : ℕ) (encode : α → List Bool)
    (xs : List α) (r : RecordedDictionary.State α)
    (hw : ∀ x ∈ xs, (encode x).length = width) :
    (recordedFold C encode xs r).2 ≤ (2 * width + 11) * xs.length := by
  induction xs generalizing r with
  | nil => simp [recordedFold]
  | cons x xs ih =>
    have hc := recordedFeed_work C encode x r
    rw [hw x (by simp)] at hc
    have hr := ih (recordedFeed C encode x r).1 (fun y hy => hw y (by simp [hy]))
    simp only [recordedFold, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

end LowSpaceSubsetSum.CountedTrie

end OAI
