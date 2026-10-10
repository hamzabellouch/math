import Mathlib.Data.Tree.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace OAI

/-!
# A finite code for rooted ordered forests

First-child / next-sibling representation turns a rooted ordered forest
into a binary tree. One bit records a leaf; a nonleaf uses a marker and a
vertex-type bit. The resulting code has exactly `3*n+1` bits.
-/

namespace TwoPointCorrelations

open BinaryTree

/-- Prefix encoding of a typed plane forest in binary-tree representation. -/
def forestBits : BinaryTree Bool → List Bool
  | .nil => [false]
  | .node b l r => true :: b :: (forestBits l ++ forestBits r)

@[simp] theorem forestBits_length (t : BinaryTree Bool) :
    (forestBits t).length = 3 * t.numNodes + 1 := by
  induction t with
  | nil => rfl
  | node b l r hl hr => simp only [forestBits, List.length_cons, List.length_append,
      hl, hr, numNodes]; omega

/-- Fuel is the maximal number of nested nodes plus one. -/
def parseForestBits : ℕ → List Bool → Option (BinaryTree Bool × List Bool)
  | 0, _ => none
  | _ + 1, false :: rest => some (.nil, rest)
  | fuel + 1, true :: b :: rest => do
      let (l, rest') ← parseForestBits fuel rest
      let (r, rest'') ← parseForestBits fuel rest'
      some (.node b l r, rest'')
  | _ + 1, _ => none

theorem parseForestBits_encode (t : BinaryTree Bool) (fuel : ℕ)
    (hf : t.numNodes < fuel) (rest : List Bool) :
    parseForestBits fuel (forestBits t ++ rest) = some (t, rest) := by
  induction t generalizing fuel rest with
  | nil =>
      cases fuel with
      | zero => simp only [numNodes] at hf; omega
      | succ fuel => rfl
  | node b l r hl hr =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hlf : l.numNodes < fuel := by simp only [numNodes] at hf; omega
          have hrf : r.numNodes < fuel := by simp only [numNodes] at hf; omega
          simp [forestBits, List.append_assoc, parseForestBits, hl fuel hlf, hr fuel hrf]

/-- Padding to a common length preserves injectivity, since parsing stops
at the exact end of the represented tree. -/
def paddedForestBits (N : ℕ) (t : BinaryTree Bool) : List Bool :=
  forestBits t ++ List.replicate (3 * (N - t.numNodes)) false

lemma paddedForestBits_length (N : ℕ) (t : BinaryTree Bool) (ht : t.numNodes ≤ N) :
    (paddedForestBits N t).length = 3 * N + 1 := by
  simp only [paddedForestBits, List.length_append, forestBits_length, List.length_replicate]
  omega

theorem paddedForestBits_injective (N : ℕ) :
    Function.Injective (fun t : {t : BinaryTree Bool // t.numNodes ≤ N} =>
      paddedForestBits N t.val) := by
  intro t u heq
  apply Subtype.ext
  have hp := congrArg (parseForestBits (N + 1)) heq
  simp only [paddedForestBits] at hp
  rw [parseForestBits_encode _ _ (by omega),
    parseForestBits_encode _ _ (by omega)] at hp
  exact congrArg Prod.fst (Option.some.inj hp)

/-- Fixed-length bit vectors enumerate every forest with at most `N` vertices. -/
def boundedForestCode (N : ℕ) (t : {t : BinaryTree Bool // t.numNodes ≤ N}) :
    Fin (3 * N + 1) → Bool :=
  fun i => (paddedForestBits N t.val).get
    ⟨i, by rw [paddedForestBits_length N t.val t.property]; exact i.isLt⟩

theorem boundedForestCode_injective (N : ℕ) : Function.Injective (boundedForestCode N) := by
  intro t u heq
  apply paddedForestBits_injective N
  apply List.ext_get
  · rw [paddedForestBits_length N t.val t.property,
      paddedForestBits_length N u.val u.property]
  · intro i ht hu
    have hi : i < 3 * N + 1 := by simpa only [paddedForestBits_length N t.val t.property] using ht
    exact congrFun heq ⟨i, hi⟩

/-- Exponential, coefficient-independent count for typed plane-forest shapes. -/
theorem card_bounded_forests (N : ℕ) :
    Nat.card {t : BinaryTree Bool // t.numNodes ≤ N} ≤ 2 ^ (3 * N + 1) := by
  have h := Nat.card_le_card_of_injective (boundedForestCode N) (boundedForestCode_injective N)
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using h

end TwoPointCorrelations

end OAI
