import OAI.Combinatorics.LowSpaceSubsetSum.Streams.RecordedDictionary

namespace OAI

/-! # Counted trie operations and a cached distinct-key count

The capacity test uses the cached count. It does not traverse the whole trie
to recompute `entries` after insertion. Equality to the dictionary
specification follows from the fixed-width insertion theorem.
-/

namespace LowSpaceSubsetSum.CountedTrie

open BinaryTrie

def contains : Tree → List Bool → Bool × ℕ
  | .empty, _ => (false, 1)
  | .leaf, [] => (true, 1)
  | .leaf, _ :: _ => (false, 1)
  | .node _ _, [] => (false, 1)
  | .node zero one, b :: key =>
    let rest := contains (if b then one else zero) key
    (rest.1, rest.2 + 1)

theorem contains_value (t : Tree) (key : List Bool) :
    (contains t key).1 = BinaryTrie.contains t key := by
  induction key generalizing t with
  | nil => cases t <;> rfl
  | cons b key ih => cases t <;> simp only [contains, BinaryTrie.contains, ih]

theorem contains_work (t : Tree) (key : List Bool) :
    (contains t key).2 ≤ key.length + 1 := by
  induction key generalizing t with
  | nil => cases t <;> simp [contains]
  | cons b key ih =>
    cases t with
    | empty => simp [contains]
    | leaf => simp [contains]
    | node zero one => simpa only [contains, List.length_cons] using Nat.add_le_add_right (ih _) 1

def insert : Tree → List Bool → Tree × ℕ
  | _, [] => (.leaf, 1)
  | .node zero one, b :: key =>
    if b then
      let rest := insert one key
      (.node zero rest.1, rest.2 + 1)
    else
      let rest := insert zero key
      (.node rest.1 one, rest.2 + 1)
  | _, b :: key =>
    let rest := insert .empty key
    (if b then .node .empty rest.1 else .node rest.1 .empty, rest.2 + 1)

theorem insert_value (t : Tree) (key : List Bool) :
    (insert t key).1 = BinaryTrie.insert t key := by
  induction key generalizing t with
  | nil => cases t <;> rfl
  | cons b key ih => cases t <;> cases b <;> simp only [insert, BinaryTrie.insert, ih, Bool.false_eq_true, ↓reduceIte]

theorem insert_work (t : Tree) (key : List Bool) :
    (insert t key).2 = key.length + 1 := by
  induction key generalizing t with
  | nil => cases t <;> rfl
  | cons b key ih => cases t <;> cases b <;> simp only [insert, ih, List.length_cons, Bool.false_eq_true, ↓reduceIte]

structure Cached where
  state : BuildResult
  count : ℕ

def feed (C : ℕ) (key : List Bool) (r : Cached) : Cached × ℕ :=
  if r.state.overflow then (r, 1) else
    let seen := contains r.state.tree key
    if seen.1 then (⟨tick r.state, r.count⟩, seen.2 + 3) else
      let next := insert r.state.tree key
      (⟨⟨next.1, decide (C < r.count + 1), r.state.processed + 1⟩, r.count + 1⟩,
        seen.2 + next.2 + 6)

theorem feed_work (C : ℕ) (key : List Bool) (r : Cached) :
    (feed C key r).2 ≤ 2 * key.length + 8 := by
  have hc := contains_work r.state.tree key
  have hi := insert_work r.state.tree key
  simp only [feed]
  split
  · omega
  · split <;> dsimp only <;> omega

theorem feed_state {C width : ℕ} (key : List Bool) (r : Cached)
    (hw : HasWidth r.state.tree width) (hk : key.length = width)
    (hcount : r.count = entries r.state.tree) :
    (feed C key r).1.state = BinaryTrie.feed C key r.state := by
  simp only [feed, contains_value, insert_value]
  by_cases ho : r.state.overflow = true
  · simp only [ho, ↓reduceIte, BinaryTrie.feed]
  · have hf : r.state.overflow = false := Bool.eq_false_iff.mpr ho
    simp only [hf, Bool.false_eq_true, ↓reduceIte, BinaryTrie.feed]
    split
    · rfl
    · rename_i hn
      have he := entries_insert hw hk
      have hc : BinaryTrie.contains r.state.tree key = false := Bool.eq_false_iff.mpr hn
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at he
      rw [he, hcount]

theorem feed_count {C width : ℕ} (key : List Bool) (r : Cached)
    (hw : HasWidth r.state.tree width) (hk : key.length = width)
    (hcount : r.count = entries r.state.tree) :
    (feed C key r).1.count = entries (feed C key r).1.state.tree := by
  simp only [feed, contains_value, insert_value]
  by_cases ho : r.state.overflow = true
  · simpa only [ho, ↓reduceIte] using hcount
  · have hf : r.state.overflow = false := Bool.eq_false_iff.mpr ho
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    split
    · exact hcount
    · rename_i hn
      have he := entries_insert hw hk
      have hc : BinaryTrie.contains r.state.tree key = false := Bool.eq_false_iff.mpr hn
      simpa only [hc, Bool.false_eq_true, ↓reduceIte, ← hcount] using he.symm

end LowSpaceSubsetSum.CountedTrie

end OAI
