import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkFrames

namespace OAI

/-! # The moving construction and the exposed bulk tree use one preorder -/

namespace Ostmann
open scoped Classical

theorem movingBulkProducts_get_path {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (bulk : TreeLeafTuple (List σ) n) (path : List Bool) (hp : path.length < n) :
    movingBulkProducts value n bulk path =
      (actualChildProducts n (movingSlotValues value n bulk)).getD
        (nodePathIndex n path) (1, 1) := by
  induction n generalizing path with
  | zero => simp at hp
  | succ n ih =>
    cases path with
    | nil =>
      simp only [movingBulkProducts, nodePathIndex, movingSlotValues, actualChildProducts,
        List.getD_cons_zero, movingSlotValues_flatten]
    | cons b path =>
      have hp' : path.length < n := by simpa using hp
      have hidx := nodePathIndex_lt n path hp'
      have hpow := Nat.one_le_two_pow (n := n)
      cases b
      · simp only [movingBulkProducts, nodePathIndex, Bool.false_eq_true, ite_false,
          movingSlotValues, actualChildProducts]
        rw [show 1 + nodePathIndex n path = nodePathIndex n path + 1 by omega,
          List.getD_cons_succ, List.getD_append _ _ _ _ (by
            rw [actualChildProducts_length]; exact hidx)]
        exact ih bulk.1 path hp'
      · simp only [movingBulkProducts, nodePathIndex, ite_true,
          movingSlotValues, actualChildProducts]
        rw [show 2 ^ n + nodePathIndex n path = (2 ^ n - 1 + nodePathIndex n path) + 1 by omega,
          List.getD_cons_succ, List.getD_append_right _ _ _ _ (by
            rw [actualChildProducts_length]; omega), actualChildProducts_length]
        rw [show 2 ^ n - 1 + nodePathIndex n path - (2 ^ n - 1) = nodePathIndex n path by omega]
        exact ih bulk.2 path hp'

theorem movingBulkProducts_preorder {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (bulk : TreeLeafTuple (List σ) n) (j : Fin (2 ^ n - 1)) :
    movingBulkProducts value n bulk (preorderNodePath n j) =
      (actualChildProducts n (movingSlotValues value n bulk)).getD j.val (1, 1) := by
  rw [movingBulkProducts_get_path value n bulk _ (preorderNodePath_length n j),
    nodePathIndex_preorderNodePath]

theorem treeLeafProduct_intCast (n : ℕ) (x : TreeLeafTuple ℕ n) :
    treeLeafProduct n (treeLeafMap (fun a : ℕ => (a : ℤ)) n x) =
      ((treeLeafProduct n x : ℕ) : ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [treeLeafProduct, treeLeafMap, ih, Nat.cast_mul]

theorem actualChildProducts_intCast (n : ℕ) (x : TreeLeafTuple ℕ n) :
    actualChildProducts n (treeLeafMap (fun a : ℕ => (a : ℤ)) n x) =
      (actualChildProducts n x).map (fun a => ((a.1 : ℤ), (a.2 : ℤ))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [treeLeafMap, actualChildProducts, treeLeafProduct_intCast, ih,
      List.map_cons, List.map_append]

theorem movingBulkProducts_preorder_intCast {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (bulk : TreeLeafTuple (List σ) n) (j : Fin (2 ^ n - 1)) :
    let b := movingBulkProducts value n bulk (preorderNodePath n j)
    ((b.1 : ℤ), (b.2 : ℤ)) =
      (actualChildProducts n (treeLeafMap (fun a : ℕ => (a : ℤ)) n
        (movingSlotValues value n bulk))).getD j.val (1, 1) := by
  rw [actualChildProducts_intCast, movingBulkProducts_preorder]
  exact (List.getD_map _ (1, 1) (fun a : ℕ × ℕ => ((a.1 : ℤ), (a.2 : ℤ)))).symm

end Ostmann

end OAI
