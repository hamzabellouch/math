import OAI.NumberTheory.Ostmann.Arithmetic.MovingFieldGiant
import OAI.NumberTheory.Ostmann.Arithmetic.MovingModularSpectator
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleSpectator

namespace OAI

/-! # The separated spectator factor on every field residue pair -/

namespace Ostmann
open scoped Classical

@[simp] theorem MovingGiantTree.castConstant_fieldAmplitude {q : ℕ} [Fact q.Prime]
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ) {n C E : ℕ} (h : C = E)
    (T : MovingGiantTree n C) (x y : ZMod q) (bulk : TreeLeafTuple (ZMod q)ˣ n) :
    movingFieldGiantAmplitude g D (T.castConstant h) x y bulk =
      movingFieldGiantAmplitude g D T x y bulk := by
  subst E
  rfl

theorem buildMovingSlotData_modular_spectator {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (D : (ZMod q)ˣ) (n : ℕ)
    (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (x y : ZMod q)
    (z : TreeLeafTuple (ZMod q)ˣ n)
    (hz : TreeNaturalLift n (movingSlotValues value n bulk) z) :
    movingModularSpectator value q g D (buildMovingSlotData n t small bulk samples) x y =
      movingFieldGiantAmplitude g D
        (buildMovingGiantTree n t (movingSlotValues value n small) (samples.values value)) x y z := by
  induction samples generalizing x y with
  | leaf =>
    change (MovingSlotReversal.naturalProduct value (show List σ from bulk) : ZMod q) =
      (show (ZMod q)ˣ from z) at hz
    simp only [buildMovingSlotData, movingModularSpectator, MovingSampleSlots.values,
      buildMovingGiantTree, movingFieldGiantAmplitude, movingSlotValues, treeLeafProduct,
      flattenMovingSlots, movingNaturalProduct_append, Nat.cast_mul, hz]
    congr 2
    ring
  | @node n samples left right ihL ihR =>
    change TreeNaturalLift n (movingSlotValues value n bulk.1) z.1 ∧
      TreeNaturalLift n (movingSlotValues value n bulk.2) z.2 at hz
    let u := movingCompensationSlots n samples
    let L := buildMovingSlotData n t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1 left
    let R := buildMovingSlotData n t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2 right
    let p := (MovingSlotData.step t.1
      (flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1)
      (flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2)
      (flattenMovingSlots n u) L R false).modularPivot value q x y
    have hp : p = reconstructedEntry (t.1 : ZMod q)
        ((frequencyRoot n t.2.1 : ℤ) : ZMod q) ((frequencyRoot n t.2.2 : ℤ) : ZMod q)
        (treeLeafProduct n (compensationLeafProducts n (movingCompensationValues value n samples)) : ℕ)
        (x * (treeLeafProduct n (movingSlotValues value n small.1) : ℕ) *
          (treeLeafProduct n z.1 : (ZMod q)ˣ))
        (y * (treeLeafProduct n (movingSlotValues value n small.2) : ℕ) *
          (treeLeafProduct n z.2 : (ZMod q)ˣ)) := by
      simp only [p, L, R, MovingSlotReversal.modularPivot, MovingSlotData.step,
        buildMovingSlotData_frequency, movingNaturalProduct_append, movingSlotValues_flatten,
        reconstructedEntry, Nat.cast_mul]
      rw [hz.1.product, hz.2.product, ← movingCompensationValues_product]
      congr 1
      ring
    have hL := ihL t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1 p x z.1 hz.1
    have hR := ihR t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2 p y z.2 hz.2
    change (if p = 0 then 0 else
      movingModularSpectator value q g D L p x * star (movingModularSpectator value q g D R p y)) = _
    rw [hL, hR]
    simp only [buildMovingGiantTree, MovingSampleSlots.values, movingSlotValues,
      movingFieldGiantAmplitude, MovingGiantTree.castConstant_frequency,
      buildMovingGiantTree_frequency, MovingGiantTree.castConstant_fieldAmplitude]
    rw [← hp]
    dsimp only [u]
    rw [movingSlotValues_append, movingSlotValues_append, movingCompensationValues_product]
    rfl

end Ostmann

end OAI
