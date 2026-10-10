import Mathlib
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A finite binary dictionary for gathered and globally memoized inputs.
Each recursive step reads one key bit and touches one node. The explicit
counters charge pointer/node operations; multiword key/value processing
is accounted for separately by their bit lengths. -/

namespace EditApproximation



namespace BinaryMemo

variable {α : Type*}











@[simp] theorem lookup_insert_same (tree : BinaryMemo α) (key : List Bool) (a : α) :
    (tree.insert key a).lookup key = some a := by
  induction key generalizing tree with
  | nil => rfl
  | cons b rest ih => cases b <;> simpa only [insert, lookup, left, right] using ih _

theorem lookup_insert_other (tree : BinaryMemo α) (key query : List Bool) (a : α)
    (hne : query ≠ key) : (tree.insert key a).lookup query = tree.lookup query := by
  induction key generalizing tree query with
  | nil =>
    cases query with
    | nil => exact False.elim (hne rfl)
    | cons b rest => cases b <;> rfl
  | cons b rest ih =>
    cases query with
    | nil => cases b <;> rfl
    | cons c tail =>
      cases b <;> cases c
      · exact ih tree.left tail (fun h => hne (congrArg (List.cons false) h))
      · rfl
      · rfl
      · exact ih tree.right tail (fun h => hne (congrArg (List.cons true) h))

@[simp] theorem lookup_empty (key : List Bool) : (empty : BinaryMemo α).lookup key = none := by
  induction key with
  | nil => rfl
  | cons b rest ih => cases b <;> exact ih

def nodes : BinaryMemo α → ℕ
  | .empty => 0
  | .node _ l r => 1 + l.nodes + r.nodes

theorem child_nodes (tree : BinaryMemo α) :
    tree.left.nodes + tree.right.nodes ≤ tree.nodes := by
  cases tree <;> simp only [left, right, nodes] <;> omega

theorem insert_nodes (tree : BinaryMemo α) (key : List Bool) (a : α) :
    (tree.insert key a).nodes ≤ tree.nodes + key.length + 1 := by
  induction key generalizing tree with
  | nil =>
    have h := child_nodes tree
    simp only [insert, nodes, List.length_nil]
    omega
  | cons b rest ih =>
    have h := child_nodes tree
    cases b
    · have hi := ih tree.left
      simp only [insert, nodes, List.length_cons]
      omega
    · have hi := ih tree.right
      simp only [insert, nodes, List.length_cons]
      omega

/-- An instrumented lookup returns exactly the ordinary dictionary
answer, charging one node visit per consumed bit and one terminal visit. -/


theorem lookupCosted_spec (tree : BinaryMemo α) (key : List Bool) :
    tree.lookupCosted key = (tree.lookup key, key.length + 1) := by
  induction key generalizing tree with
  | nil => rfl
  | cons b rest ih => cases b <;> simp only [lookupCosted, lookup, ih, List.length_cons]

/-- Persistent insertion allocates one new node at each visited level;
the two untouched subtrees are retained by pointer. -/


theorem insertCosted_spec (tree : BinaryMemo α) (key : List Bool) (a : α) :
    tree.insertCosted key a = (tree.insert key a, key.length + 1) := by
  induction key generalizing tree with
  | nil => rfl
  | cons b rest ih => cases b <;> simp only [insertCosted, insert, ih, List.length_cons]

end BinaryMemo

/-- Fixed-width, least-significant-bit first encoding; no allocation
proportional to the numerical magnitude of a key is required. -/


@[simp] theorem binaryMemoKey_length (d n : ℕ) : (binaryMemoKey d n).length = d := by
  induction d generalizing n with
  | zero => rfl
  | succ d ih => simp only [binaryMemoKey, List.length_cons, ih]

theorem binaryMemoKey_injective (d : ℕ) :
    Set.InjOn (binaryMemoKey d) {n | n < 2 ^ d} := by
  induction d with
  | zero => intro n hn m hm _; simp only [pow_zero, Set.mem_ofPred_eq] at hn hm; omega
  | succ d ih =>
    intro n hn m hm heq
    have hpair := List.cons.inj heq
    have hmod : n % 2 = m % 2 := by
      have hiff := decide_eq_decide.mp hpair.1
      omega
    have hnq : n / 2 < 2 ^ d := by
      simp only [Set.mem_ofPred_eq, pow_succ] at hn
      omega
    have hmq : m / 2 < 2 ^ d := by
      simp only [Set.mem_ofPred_eq, pow_succ] at hm
      omega
    have hquot := ih hnq hmq hpair.2
    omega

theorem binaryMemo_lookup_insert {α : Type*} (tree : BinaryMemo α)
    (d key query : ℕ) (hkey : key < 2 ^ d) (hquery : query < 2 ^ d) (a : α) :
    (tree.insert (binaryMemoKey d key) a).lookup (binaryMemoKey d query) =
      if query = key then some a else tree.lookup (binaryMemoKey d query) := by
  split_ifs with heq
  · subst query
    exact BinaryMemo.lookup_insert_same _ _ _
  · apply BinaryMemo.lookup_insert_other
    intro hencoded
    exact heq (binaryMemoKey_injective d hquery hkey hencoded)

end EditApproximation

end OAI
