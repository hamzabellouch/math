import OAI.Combinatorics.EditApproximation.Binary.BinaryMemo
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Cached binary position counts. Inserting a position and counting positions
strictly below a boundary both follow one root-to-leaf path. Counts are stored
at internal nodes, so a prefixCount query does not traverse a whole interval. -/

namespace EditApproximation



namespace PositionCounts









@[simp] theorem count_add (tree : PositionCounts) (d i : ℕ) :
    (tree.add d i).count = tree.count + 1 := by
  cases d with
  | zero => rfl
  | succ d =>
    simp only [add]
    split_ifs <;> rfl

def prefixCount (tree : PositionCounts) : ℕ → ℕ → ℕ
  | 0, t => if t = 0 then 0 else tree.count
  | d + 1, t =>
    if t ≤ 2 ^ d then tree.left.prefixCount d t
    else tree.left.count + tree.right.prefixCount d (t - 2 ^ d)

@[simp] theorem prefix_empty (d t : ℕ) : prefixCount .empty d t = 0 := by
  induction d generalizing t with
  | zero => simp only [prefixCount, count, ite_self]
  | succ d ih => simp only [prefixCount, left, right, count, ih, zero_add, ite_self]

/-- Adding one stored position changes a prefixCount count by exactly its
membership indicator. This holds for any prior tree, without a balance
or density assumption. -/
theorem prefix_add (tree : PositionCounts) (d i t : ℕ) (hi : i < 2 ^ d) :
    (tree.add d i).prefixCount d t = tree.prefixCount d t + if i < t then 1 else 0 := by
  induction d generalizing tree i t with
  | zero =>
    have hi0 : i = 0 := by simpa using hi
    subst i
    by_cases ht : t = 0
    · subst t; simp only [prefixCount, add, count, lt_self_iff_false, ite_true, ite_false, add_zero]
    · have hpos : 0 < t := Nat.pos_of_ne_zero ht
      simp only [prefixCount, add, count, ht, hpos, ite_false, ite_true]
  | succ d ih =>
    have hi' : i < 2 ^ d * 2 := by simpa only [pow_succ] using hi
    by_cases hip : i < 2 ^ d
    · by_cases htp : t ≤ 2 ^ d
      · simpa only [add, hip, ite_true, prefixCount, htp, left] using ih tree.left i t hip
      · have hit : i < t := by omega
        simp only [add, hip, ite_true, prefixCount, htp, ite_false, left, right, count_add, hit]
        omega
    · have hir : i - 2 ^ d < 2 ^ d := by omega
      by_cases htp : t ≤ 2 ^ d
      · have hit : ¬ i < t := by omega
        simp only [add, hip, ite_false, prefixCount, htp, ite_true, left, hit, add_zero]
      · have heq : i - 2 ^ d < t - 2 ^ d ↔ i < t := by omega
        simp only [add, hip, ite_false, prefixCount, htp, left, right, ih _ _ _ hir, heq]
        omega



theorem addWithWork_spec (tree : PositionCounts) (d i : ℕ) :
    tree.addWithWork d i = (tree.add d i, 2 * d + 1) := by
  induction d generalizing tree i with
  | zero => rfl
  | succ d ih =>
    simp only [addWithWork, add]
    split_ifs <;> rw [ih] <;> simp only <;> congr 1



theorem prefixWithWork_spec (tree : PositionCounts) (d t : ℕ) :
    tree.prefixWithWork d t = (tree.prefixCount d t, 2 * d + 1) := by
  induction d generalizing tree t with
  | zero => rfl
  | succ d ih =>
    simp only [prefixWithWork, prefixCount]
    split_ifs <;> rw [ih] <;> simp only <;> congr 1

def nodes : PositionCounts → ℕ
  | .empty => 0
  | .node _ l r => 1 + l.nodes + r.nodes

theorem children_nodes (tree : PositionCounts) :
    tree.left.nodes + tree.right.nodes ≤ tree.nodes := by
  cases tree <;> simp only [left, right, nodes] <;> omega

theorem add_nodes (tree : PositionCounts) (d i : ℕ) :
    (tree.add d i).nodes ≤ tree.nodes + d + 1 := by
  induction d generalizing tree i with
  | zero =>
    have h := children_nodes tree
    simp only [add, nodes]
    omega
  | succ d ih =>
    have h := children_nodes tree
    simp only [add]
    split_ifs
    · have hrec := ih tree.left i
      simp only [nodes]
      omega
    · have hrec := ih tree.right (i - 2 ^ d)
      simp only [nodes]
      omega

end PositionCounts

end EditApproximation

end OAI
