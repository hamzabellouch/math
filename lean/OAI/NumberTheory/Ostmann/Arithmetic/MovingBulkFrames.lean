import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantAncestorValues

namespace OAI

/-! # Fixed nonbulk factors and literal bulk products at each moving node -/

namespace Ostmann
open scoped Classical

structure MovingFrameConstants where
  leftSmall : ℕ
  rightSmall : ℕ
  compensation : ℕ

/-- These factors are computed from the fixed small and internal samples;
no bulk coordinate or giant value is used. -/
def movingFrameConstants {σ : Type*} (value : σ → ℕ) :
    (n : ℕ) → TreeLeafTuple (List σ) n → MovingSampleSlots σ n →
      List Bool → MovingFrameConstants
  | 0, _, .leaf, _ => ⟨1, 1, 1⟩
  | n + 1, small, .node a l r, path =>
      let u := movingCompensationSlots n a
      match path with
      | [] => ⟨MovingSlotReversal.naturalProduct value (flattenMovingSlots n small.1),
          MovingSlotReversal.naturalProduct value (flattenMovingSlots n small.2),
          MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)⟩
      | false :: path => movingFrameConstants value n (appendMovingSlotLeaves n u small.1) l path
      | true :: path => movingFrameConstants value n (appendMovingSlotLeaves n u small.2) r path

/-- The two child bulk products in the same root-to-node order. -/
def movingBulkProducts {σ : Type*} (value : σ → ℕ) :
    (n : ℕ) → TreeLeafTuple (List σ) n → List Bool → ℕ × ℕ
  | 0, _, _ => (1, 1)
  | n + 1, bulk, [] =>
      (MovingSlotReversal.naturalProduct value (flattenMovingSlots n bulk.1),
        MovingSlotReversal.naturalProduct value (flattenMovingSlots n bulk.2))
  | n + 1, bulk, false :: path => movingBulkProducts value n bulk.1 path
  | n + 1, bulk, true :: path => movingBulkProducts value n bulk.2 path

/-- Every actual transfer node has its fixed small factor, its current giant,
and precisely the bulk product from its own child subtree. -/
theorem movingNodeAtPath_products {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n)
    (XL XR : ℕ) (path : List Bool) (hp : path.length < n) :
    let z := (transferNodeAtPath (movingSlotSystem value childBound pivotBound) n
      ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t path).state
    let c := movingFrameConstants value n small a path
    let b := movingBulkProducts value n bulk path
    z.compensation value = c.compensation ∧
      z.leftProduct value = z.leftGiant * c.leftSmall * b.1 ∧
      z.rightProduct value = z.rightGiant * c.rightSmall * b.2 := by
  induction n generalizing XL XR path with
  | zero => simp at hp
  | succ n ih =>
    cases a with
    | node a l r =>
      cases path with
      | nil =>
        simp only [transferNodeAtPath, buildMovingSlotData, movingFrameConstants,
          movingBulkProducts, MovingSlotState.compensation, MovingSlotState.leftProduct,
          MovingSlotState.rightProduct, movingNaturalProduct_append, Nat.mul_assoc, and_self]
      | cons b path =>
        have hp' : path.length < n := by simpa using hp
        let sys := movingSlotSystem value childBound pivotBound
        let u := movingCompensationSlots n a
        let x : MovingSlotState σ :=
          ⟨n + 1, buildMovingSlotData (n + 1) t small bulk (.node a l r), XL, XR⟩
        let p := historyPivot sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) /
          MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)
        cases b
        · exact ih t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1 l p XL path hp'
        · exact ih t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2 r p XR path hp'

end Ostmann

end OAI
