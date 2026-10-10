import OAI.NumberTheory.Ostmann.Construction.ScheduledPreorderNodes
import OAI.NumberTheory.Ostmann.Construction.ScaledWordLeaves
import OAI.NumberTheory.Ostmann.Characters.TreeSplitResidues

namespace OAI

/-! # Preorder child products of the selected original prime leaves -/

namespace Ostmann
open scoped BigOperators

theorem treeLeafProduct_indexed {G : Type*} [CommMonoid G]
    (n : ℕ) (x : TreeLeafIndex n → G) :
    treeLeafProduct n ((treeLeafTupleEquiv G n).symm x) = ∏ i, x i := by
  induction n with
  | zero =>
    change Unit → G at x
    change x () = ∏ i : Unit, x i
    exact (Fintype.prod_subsingleton x ()).symm
  | succ n ih =>
    change (TreeLeafIndex n ⊕ TreeLeafIndex n) → G at x
    change treeLeafProduct n ((treeLeafTupleEquiv G n).symm (fun i => x (.inl i))) *
      treeLeafProduct n ((treeLeafTupleEquiv G n).symm (fun i => x (.inr i))) = _
    rw [ih, ih]
    change _ = ∏ i : TreeLeafIndex n ⊕ TreeLeafIndex n, x i
    exact (Fintype.prod_sum_type x).symm

def childProductsAtPath {G : Type*} [CommMonoid G] :
    (n : ℕ) → TreeLeafTuple G n → List Bool → G × G
  | 0, _, _ => (1, 1)
  | n + 1, x, [] => (treeLeafProduct n x.1, treeLeafProduct n x.2)
  | n + 1, x, b :: path =>
      if b then childProductsAtPath n x.2 path else childProductsAtPath n x.1 path

theorem actualChildProducts_get_path {G : Type*} [CommMonoid G]
    (n : ℕ) (x : TreeLeafTuple G n) (path : List Bool) (hp : path.length < n) :
    (actualChildProducts n x).getD (nodePathIndex n path) (1, 1) =
      childProductsAtPath n x path := by
  induction n generalizing path with
  | zero => simp at hp
  | succ n ih =>
    cases path with
    | nil => rfl
    | cons b path =>
      have hp' : path.length < n := by simpa using hp
      have hidx := nodePathIndex_lt n path hp'
      have hpow := Nat.one_le_two_pow (n := n)
      cases b
      · simp only [nodePathIndex, Bool.false_eq_true, ite_false, actualChildProducts]
        rw [show 1 + nodePathIndex n path = nodePathIndex n path + 1 by omega,
          List.getD_cons_succ, List.getD_append _ _ _ _ (by
            rw [actualChildProducts_length]; exact hidx)]
        exact ih _ path hp'
      · simp only [nodePathIndex, ite_true, actualChildProducts]
        rw [show 2 ^ n + nodePathIndex n path = (2 ^ n - 1 + nodePathIndex n path) + 1 by omega,
          List.getD_cons_succ, List.getD_append_right _ _ _ _ (by
            rw [actualChildProducts_length]; omega), actualChildProducts_length]
        rw [show 2 ^ n - 1 + nodePathIndex n path - (2 ^ n - 1) = nodePathIndex n path by omega]
        exact ih _ path hp'

theorem childProductsAtPath_descend {G : Type*} [CommMonoid G]
    (n : ℕ) (path : List Bool) (x : TreeLeafIndex (n + 1 + path.length) → G) :
    childProductsAtPath (n + 1 + path.length)
      ((treeLeafTupleEquiv G (n + 1 + path.length)).symm x) path =
        (∏ i : TreeLeafIndex n, descendLeafValues path.length (n + 1) (reversePathOfList path) x (.inl i),
         ∏ i : TreeLeafIndex n, descendLeafValues path.length (n + 1) (reversePathOfList path) x (.inr i)) := by
  induction path with
  | nil =>
    change (treeLeafProduct n ((treeLeafTupleEquiv G n).symm (fun i => x (.inl i))),
      treeLeafProduct n ((treeLeafTupleEquiv G n).symm (fun i => x (.inr i)))) = _
    rw [treeLeafProduct_indexed, treeLeafProduct_indexed]
    rfl
  | cons b path ih =>
    cases b
    · change childProductsAtPath (n + 1 + path.length)
        ((treeLeafTupleEquiv G (n + 1 + path.length)).symm (fun i => x (.inl i))) path = _
      rw [ih]
      rfl
    · change childProductsAtPath (n + 1 + path.length)
        ((treeLeafTupleEquiv G (n + 1 + path.length)).symm (fun i => x (.inr i))) path = _
      rw [ih]
      rfl

end Ostmann

end OAI
