import OAI.NumberTheory.Ostmann.Arithmetic.NodeBulkProducts
import OAI.NumberTheory.Ostmann.Construction.ScheduledNodeFrequencies

namespace OAI

/-! # The two sampled prime products at each actual scheduled node -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def scheduledNodeLeafValues {G : Type*} (n : ℕ) (j : Fin (2 ^ n - 1))
    (x : TreeLeafIndex n → G) : TreeLeafIndex (scheduledNodeLevel n j + 1) → G :=
  descendLeafValues (preorderNodePath n j).length (scheduledNodeLevel n j + 1)
    (scheduledReversePath n j)
    (fun v => x (Equiv.cast (congrArg TreeLeafIndex (scheduledNodeLevel_add_depth n j)) v))

theorem scheduledNodeLeafValues_products {G : Type*} [CommMonoid G]
    (n : ℕ) (j : Fin (2 ^ n - 1)) (x : TreeLeafIndex n → G) :
    (actualChildProducts n ((treeLeafTupleEquiv G n).symm x)).getD j.val (1, 1) =
      (∏ i : TreeLeafIndex (scheduledNodeLevel n j), scheduledNodeLeafValues n j x (.inl i),
       ∏ i : TreeLeafIndex (scheduledNodeLevel n j), scheduledNodeLeafValues n j x (.inr i)) := by
  have hcast : ∀ {a b : ℕ} (e : a = b) (x : TreeLeafIndex b → G) (path : List Bool),
      childProductsAtPath a ((treeLeafTupleEquiv G a).symm
        (fun v => x (Equiv.cast (congrArg TreeLeafIndex e) v))) path =
      childProductsAtPath b ((treeLeafTupleEquiv G b).symm x) path := by
    intro a b e x path
    subst b
    rfl
  rw [← nodePathIndex_preorderNodePath n j,
    actualChildProducts_get_path n _ _ (preorderNodePath_length n j)]
  rw [← hcast (scheduledNodeLevel_add_depth n j) x (preorderNodePath n j)]
  exact childProductsAtPath_descend _ _ _

/-- Transporting the root index does not change which word leaves scale. -/
theorem wordLeafScale_cast {I G : Type*} [Mul G]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    {a b : ℕ} (e : a = b) (C : CopyScheduleAtoms role b → G) (x : TreeLeafIndex b → G) :
    (fun v => wordLeafScale role i hi b C x
      (Equiv.cast (congrArg (CopyScheduleAtoms role) e) v)) =
      wordLeafScale role i hi a
        (fun v => C (Equiv.cast (congrArg (CopyScheduleAtoms role) e) v))
        (fun v => x (Equiv.cast (congrArg TreeLeafIndex e) v)) := by
  subst b
  rfl

theorem scheduledNodeValues_wordLeafScale {I G : Type*} [Zero G] [Mul G]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    (n : ℕ) (j : Fin (2 ^ n - 1)) (C : CopyScheduleAtoms role n → G)
    (x : TreeLeafIndex n → G) (p : Fin (2 ^ n - 1) → G) :
    scheduledNodeValues role n j (wordLeafScale role i hi n C x) p =
      wordLeafScale role i hi (scheduledNodeLevel n j + 1)
        (scheduledNodeValues role n j C p) (scheduledNodeLeafValues n j x) := by
  unfold scheduledNodeValues scheduledNodeRootEquiv
  rw [wordLeafScale_cast role i hi (scheduledNodeLevel_add_depth n j),
    descendAtomValues_wordLeafScale]
  rfl

/-- These are exactly the two bulk factors used by `SampledPivotHistory`. -/
theorem scheduledNodeValues_H_product {I G : Type*} [Fintype I] [Zero G] [CommMonoid G]
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    (n : ℕ) (j : Fin (2 ^ n - 1)) (b : Bool) (C : CopyScheduleAtoms role n → G)
    (x : TreeLeafIndex n → G) (p : Fin (2 ^ n - 1) → G) :
    (∏ a : CopyScheduleH role (scheduledNodeLevel n j),
      scheduledNodeValues role n j (wordLeafScale role i hi n C x) p
        ⟨.inl (b, a.val), a.property⟩) =
      (∏ a : CopyScheduleH role (scheduledNodeLevel n j),
        scheduledNodeValues role n j C p ⟨.inl (b, a.val), a.property⟩) *
        (if b then
          ((actualChildProducts n ((treeLeafTupleEquiv G n).symm x)).getD j.val (1, 1)).1
        else ((actualChildProducts n ((treeLeafTupleEquiv G n).symm x)).getD j.val (1, 1)).2) := by
  rw [scheduledNodeValues_wordLeafScale, wordLeafScale_H_product, scheduledNodeLeafValues_products]
  cases b <;> rfl

end Ostmann

end OAI
