import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedTrie

namespace OAI

/-! # Extra live cells of fixed-width trie lookup and insertion

The old trie is retained by the caller. Insertion allocates one new path and
shares all untouched subtrees; this trace counts that path and its recursive
frames, rather than duplicating the whole trie at every level.
-/

namespace LowSpaceSubsetSum.TrieCells

open BinaryTrie

def contains : Tree → List Bool → (Bool × ℕ) × ℕ
  | .empty, _ => ((false, 1), 4)
  | .leaf, [] => ((true, 1), 4)
  | .leaf, _ :: _ => ((false, 1), 4)
  | .node _ _, [] => ((false, 1), 4)
  | .node zero one, b :: key =>
    let rest := contains (if b then one else zero) key
    ((rest.1.1, rest.1.2 + 1), rest.2 + 2)

theorem contains_value (t : Tree) (key : List Bool) :
    (contains t key).1 = CountedTrie.contains t key := by
  induction key generalizing t with
  | nil => cases t <;> rfl
  | cons b key ih => cases t <;> simp only [contains, CountedTrie.contains, ih]

theorem contains_cells (t : Tree) (key : List Bool) :
    (contains t key).2 ≤ 2 * key.length + 4 := by
  induction key generalizing t with
  | nil => cases t <;> simp only [contains, List.length_nil] <;> omega
  | cons b key ih =>
    cases t with
    | empty => simp only [contains, List.length_cons]; omega
    | leaf => simp only [contains, List.length_cons]; omega
    | node zero one =>
      have h := ih (if b then one else zero)
      simp only [contains, List.length_cons]
      omega

def insert : Tree → List Bool → (Tree × ℕ) × ℕ
  | _, [] => ((.leaf, 1), 3)
  | .node zero one, b :: key =>
    if b then
      let rest := insert one key
      ((.node zero rest.1.1, rest.1.2 + 1), rest.2 + 5)
    else
      let rest := insert zero key
      ((.node rest.1.1 one, rest.1.2 + 1), rest.2 + 5)
  | _, b :: key =>
    let rest := insert .empty key
    ((if b then .node .empty rest.1.1 else .node rest.1.1 .empty, rest.1.2 + 1), rest.2 + 5)

theorem insert_value (t : Tree) (key : List Bool) :
    (insert t key).1 = CountedTrie.insert t key := by
  induction key generalizing t with
  | nil => cases t <;> rfl
  | cons b key ih =>
    cases t <;> cases b <;>
      simp only [insert, CountedTrie.insert, ih, Bool.false_eq_true, ↓reduceIte]

theorem insert_cells (t : Tree) (key : List Bool) :
    (insert t key).2 = 5 * key.length + 3 := by
  induction key generalizing t with
  | nil => cases t <;> rfl
  | cons b key ih =>
    cases t <;> cases b <;>
      simp only [insert, ih, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

end LowSpaceSubsetSum.TrieCells

end OAI
