import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace OAI

/-!
# Fixed-width binary dictionaries

An executable sparse binary trie for fixed-width keys, with exact membership
and insertion semantics and a node-count bound. The array of retained records
is separate; the trie is used to decide whether a key is new. This is the
bounded dictionary component in the paper's stream implementation.
-/

namespace LowSpaceSubsetSum
namespace BinaryTrie

inductive Tree where
  | empty
  | leaf
  | node (zero one : Tree)
  deriving DecidableEq

def contains : Tree → List Bool → Bool
  | .empty, _ => false
  | .leaf, [] => true
  | .leaf, _ :: _ => false
  | .node _ _, [] => false
  | .node zero one, b :: key => contains (if b then one else zero) key

def insert : Tree → List Bool → Tree
  | _, [] => .leaf
  | .node zero one, b :: key =>
      if b then .node zero (insert one key) else .node (insert zero key) one
  | _, b :: key =>
      if b then .node .empty (insert .empty key) else .node (insert .empty key) .empty

def nodes : Tree → ℕ
  | .empty => 0
  | .leaf => 1
  | .node zero one => 1 + nodes zero + nodes one

def entries : Tree → ℕ
  | .empty => 0
  | .leaf => 1
  | .node zero one => entries zero + entries one

/-- All present keys have the specified length. Empty subtrees are allowed. -/
def HasWidth : Tree → ℕ → Prop
  | .empty, _ => True
  | .leaf, width => width = 0
  | .node _ _, 0 => False
  | .node zero one, width + 1 => HasWidth zero width ∧ HasWidth one width

/-- No internal node is retained if both its branches are empty. -/
def Compact : Tree → Prop
  | .empty => True
  | .leaf => True
  | .node zero one => Compact zero ∧ Compact one ∧ (zero ≠ .empty ∨ one ≠ .empty)

theorem insert_ne_empty (t : Tree) (key : List Bool) : insert t key ≠ .empty := by
  cases key with
  | nil => simp [insert]
  | cons b key => cases t <;> cases b <;> simp [insert]

theorem entries_pos_of_ne_empty {t : Tree} (hc : Compact t) (ht : t ≠ .empty) :
    0 < entries t := by
  induction t with
  | empty => exact (ht rfl).elim
  | leaf => simp [entries]
  | node zero one ih0 ih1 =>
    obtain ⟨hc0, hc1, hne⟩ := hc
    rcases hne with h0 | h1
    · have h := ih0 hc0 h0
      simp only [entries]
      omega
    · have h := ih1 hc1 h1
      simp only [entries]
      omega

theorem insert_hasWidth {t : Tree} {key : List Bool} {width : ℕ}
    (ht : HasWidth t width) (hk : key.length = width) :
    HasWidth (insert t key) width := by
  induction key generalizing t width with
  | nil => simp_all [HasWidth, insert]
  | cons b key ih =>
    cases width with
    | zero => simp at hk
    | succ width =>
      have hk' : key.length = width := by simpa using hk
      cases t with
      | empty =>
        have he := ih (t := .empty) (width := width) trivial hk'
        cases b <;> simp [insert, HasWidth, he]
      | leaf => simp [HasWidth] at ht
      | node zero one =>
        obtain ⟨h0, h1⟩ := ht
        cases b <;> simp [insert, HasWidth, h0, h1, ih h0 hk', ih h1 hk']

theorem insert_compact {t : Tree} (ht : Compact t) (key : List Bool) :
    Compact (insert t key) := by
  induction key generalizing t with
  | nil => simp [insert, Compact]
  | cons b key ih =>
    cases t with
    | empty =>
      have he := ih (t := .empty) trivial
      cases b <;> simp [insert, Compact, he, insert_ne_empty]
    | leaf =>
      have he := ih (t := .empty) trivial
      cases b <;> simp [insert, Compact, he, insert_ne_empty]
    | node zero one =>
      obtain ⟨h0, h1, _⟩ := ht
      cases b <;> simp [insert, Compact, h0, h1, ih h0, ih h1, insert_ne_empty]

/-- The number of retained nodes is linear in key width times distinct keys. -/
theorem nodes_le_width_mul_entries {t : Tree} {width : ℕ}
    (ht : HasWidth t width) (hc : Compact t) : nodes t ≤ (width + 1) * entries t := by
  induction t generalizing width with
  | empty => simp [nodes, entries]
  | leaf => simp [nodes, entries]
  | node zero one ih0 ih1 =>
    cases width with
    | zero => exact ht.elim
    | succ width =>
      obtain ⟨hw0, hw1⟩ := ht
      obtain ⟨hc0, hc1, hne⟩ := hc
      have h0 := ih0 hw0 hc0
      have h1 := ih1 hw1 hc1
      have hp : 0 < entries (.node zero one) :=
        entries_pos_of_ne_empty ⟨hc0, hc1, hne⟩ (by simp)
      simp only [nodes, entries] at *
      nlinarith

/-- One insertion adds a key exactly when membership previously failed. -/
theorem entries_insert {t : Tree} {key : List Bool} {width : ℕ}
    (ht : HasWidth t width) (hk : key.length = width) :
    entries (insert t key) = entries t + if contains t key then 0 else 1 := by
  induction key generalizing t width with
  | nil =>
    have hw : width = 0 := by simpa using hk.symm
    subst width
    cases t <;> simp_all [insert, contains, entries, HasWidth]
  | cons b key ih =>
    cases width with
    | zero => simp at hk
    | succ width =>
      have hk' : key.length = width := by simpa using hk
      cases t with
      | empty =>
        have he := ih (t := .empty) (by trivial) hk'
        cases b <;> simp_all [insert, contains, entries]
      | leaf => simp [HasWidth] at ht
      | node zero one =>
        obtain ⟨h0, h1⟩ := ht
        have he0 := ih h0 hk'
        have he1 := ih h1 hk'
        cases b <;> simp_all [insert, contains, entries] <;> omega

/-- Exact set insertion semantics for keys of the fixed width. -/
theorem contains_insert_iff {t : Tree} {key query : List Bool} {width : ℕ}
    (ht : HasWidth t width) (hk : key.length = width) (hq : query.length = width) :
    contains (insert t key) query = true ↔ query = key ∨ contains t query = true := by
  induction key generalizing t query width with
  | nil =>
    have hw : width = 0 := by simpa using hk.symm
    subst width
    have hquery : query = [] := List.length_eq_zero_iff.mp hq
    subst query
    cases t <;> simp_all [insert, contains, HasWidth]
  | cons b key ih =>
    cases query with
    | nil => simp at hk hq; omega
    | cons qb query =>
      cases width with
      | zero => simp at hk
      | succ width =>
        have hk' : key.length = width := by simpa using hk
        have hq' : query.length = width := by simpa using hq
        cases t with
        | empty =>
          have hi := ih (t := .empty) (by trivial) hk' hq'
          cases b <;> cases qb <;> simp_all [insert, contains]
        | leaf => simp [HasWidth] at ht
        | node zero one =>
          obtain ⟨h0, h1⟩ := ht
          have hi0 := ih h0 hk' hq'
          have hi1 := ih h1 hk' hq'
          cases b <;> cases qb <;> simp_all [insert, contains]

/-- The number of nodes examined by a membership lookup. -/
def lookupSteps : Tree → List Bool → ℕ
  | .node zero one, b :: key => 1 + lookupSteps (if b then one else zero) key
  | _, _ => 1

theorem lookupSteps_le (t : Tree) (key : List Bool) :
    lookupSteps t key ≤ key.length + 1 := by
  induction key generalizing t with
  | nil => cases t <;> simp [lookupSteps]
  | cons b key ih =>
    cases t with
    | empty => simp [lookupSteps]
    | leaf => simp [lookupSteps]
    | node zero one =>
      cases b <;> simp only [lookupSteps, Bool.false_eq_true, ↓reduceIte,
        List.length_cons]
      · have h := ih zero
        omega
      · have h := ih one
        omega

theorem nodes_insert_le (t : Tree) (key : List Bool) :
    nodes (insert t key) ≤ nodes t + key.length + 1 := by
  induction key generalizing t with
  | nil => cases t <;> simp [insert, nodes]
  | cons b key ih =>
    cases t with
    | empty =>
      have h := ih .empty
      simp only [nodes] at h
      cases b <;> simp only [insert, nodes, List.length_cons,
        Bool.false_eq_true, ↓reduceIte] <;> omega
    | leaf =>
      have h := ih .empty
      simp only [nodes] at h
      cases b <;> simp only [insert, nodes, List.length_cons,
        Bool.false_eq_true, ↓reduceIte] <;> omega
    | node zero one =>
      have h0 := ih zero
      have h1 := ih one
      cases b <;> simp only [insert, nodes, List.length_cons,
        Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A hard entry capacity also bounds nodes, including a first rejected key. -/
theorem nodes_insert_le_capacity {t : Tree} {key : List Bool} {width C : ℕ}
    (ht : HasWidth t width) (hc : Compact t) (hk : key.length = width)
    (hcap : entries t ≤ C) : nodes (insert t key) ≤ (width + 1) * (C + 1) := by
  have hn := nodes_le_width_mul_entries (insert_hasWidth ht hk) (insert_compact hc key)
  have he := entries_insert ht hk
  have hnew : entries (insert t key) ≤ C + 1 := by
    rw [he]
    split <;> omega
  exact hn.trans (Nat.mul_le_mul_left (width + 1) hnew)

end BinaryTrie
end LowSpaceSubsetSum

end OAI
