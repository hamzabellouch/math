import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleSlots
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotRealization

namespace OAI

/-! # The labelled sampler evaluates to the actual natural prime sampler -/

namespace Ostmann
open scoped BigOperators

def movingSlotValues {σ : Type*} (value : σ → ℕ) : (n : ℕ) →
    TreeLeafTuple (List σ) n → TreeLeafTuple ℕ n
  | 0, x => MovingSlotReversal.naturalProduct value (show List σ from x)
  | n + 1, x => (movingSlotValues value n x.1, movingSlotValues value n x.2)

def movingCompensationValues {σ : Type*} (value : σ → ℕ) : (n : ℕ) →
    TreeLeafTuple (Fin 4 → σ) n → TreeLeafTuple (Fin 4 → ℕ) n
  | 0, x => fun i => value ((show Fin 4 → σ from x) i)
  | n + 1, x => (movingCompensationValues value n x.1, movingCompensationValues value n x.2)

def MovingSampleSlots.values {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSampleSlots σ n → MovingGiantSamples n
  | _, .leaf => .leaf
  | n + 1, .node samples left right =>
      .node (movingCompensationValues value n samples) (left.values value) (right.values value)

theorem movingNaturalProduct_append {σ : Type*} (value : σ → ℕ) (x y : List σ) :
    MovingSlotReversal.naturalProduct value (x ++ y) =
      MovingSlotReversal.naturalProduct value x * MovingSlotReversal.naturalProduct value y := by
  simp only [MovingSlotReversal.naturalProduct, List.map_append, List.prod_append]

theorem movingSlotValues_flatten {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (x : TreeLeafTuple (List σ) n) :
    MovingSlotReversal.naturalProduct value (flattenMovingSlots n x) =
      treeLeafProduct n (movingSlotValues value n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [flattenMovingSlots, MovingSlotReversal.naturalProduct, List.map_append,
      List.prod_append, movingSlotValues, treeLeafProduct]
    exact congrArg₂ (· * ·) (ih x.1) (ih x.2)

theorem movingSlotValues_append {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (x y : TreeLeafTuple (List σ) n) :
    movingSlotValues value n (appendMovingSlotLeaves n x y) =
      multiplySmallLeaves n (movingSlotValues value n x) (movingSlotValues value n y) := by
  induction n with
  | zero =>
    simp only [movingSlotValues, appendMovingSlotLeaves, multiplySmallLeaves,
      MovingSlotReversal.naturalProduct, List.map_append, List.prod_append]
  | succ n ih => exact Prod.ext (ih x.1 y.1) (ih x.2 y.2)

theorem movingCompensationValues_product {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (x : TreeLeafTuple (Fin 4 → σ) n) :
    movingSlotValues value n (movingCompensationSlots n x) =
      compensationLeafProducts n (movingCompensationValues value n x) := by
  induction n with
  | zero =>
    change ((List.ofFn (show Fin 4 → σ from x)).map value).prod = ∏ i : Fin 4, value (x i)
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  | succ n ih => exact Prod.ext (ih x.1) (ih x.2)

theorem buildMovingSlotData_frequency {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n) :
    (buildMovingSlotData n t small bulk samples).frequency = frequencyRoot n t := by
  cases samples <;> rfl

end Ostmann

end OAI
