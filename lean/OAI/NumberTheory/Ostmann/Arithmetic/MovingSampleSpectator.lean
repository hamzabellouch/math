import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotSpectator

namespace OAI

/-! # The full recursive coefficient has the constructed spectator diagram -/

namespace Ostmann
open scoped Classical

@[simp] theorem MovingGiantTree.castConstant_amplitude {q : ℕ} [Fact q.Prime]
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ) {n C E : ℕ} (h : C = E)
    (T : MovingGiantTree n C) (XL XR : ℕ) (bulk : TreeLeafTuple ℕ n) :
    movingGiantAmplitude g D (T.castConstant h) XL XR bulk =
      movingGiantAmplitude g D T XL XR bulk := by
  subst E
  rfl

theorem buildMovingSlotData_spectator {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (g : ZMod q → ℂ) (D : (ZMod q)ˣ) (n : ℕ)
    (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (XL XR : ℕ) :
    movingSlotSpectator value g D (buildMovingSlotData n t small bulk samples) XL XR =
      movingGiantAmplitude g D
        (buildMovingGiantTree n t (movingSlotValues value n small) (samples.values value))
        XL XR (movingSlotValues value n bulk) := by
  induction samples generalizing XL XR with
  | leaf =>
    simp only [buildMovingSlotData, movingSlotSpectator, MovingSampleSlots.values,
      buildMovingGiantTree, movingGiantAmplitude, movingSlotValues, treeLeafProduct,
      flattenMovingSlots, movingNaturalProduct_append, Nat.mul_assoc]
  | @node n samples left right ihL ihR =>
    let u := movingCompensationSlots n samples
    let L := buildMovingSlotData n t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1 left
    let R := buildMovingSlotData n t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2 right
    let p := (MovingSlotData.step t.1
      (flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1)
      (flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2)
      (flattenMovingSlots n u) L R false).naturalPivot value XL XR
    have hp : p = movingGiantPivot t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
        (treeLeafProduct n (movingSlotValues value n small.1))
        (treeLeafProduct n (movingSlotValues value n small.2))
        (treeLeafProduct n (compensationLeafProducts n (movingCompensationValues value n samples)))
        XL XR (treeLeafProduct n (movingSlotValues value n bulk.1))
        (treeLeafProduct n (movingSlotValues value n bulk.2)) := by
      simp only [p, L, R, MovingSlotReversal.naturalPivot, MovingSlotData.step,
        buildMovingSlotData_frequency, movingNaturalProduct_append, movingSlotValues_flatten,
        movingGiantPivot, Nat.mul_one, Nat.mul_assoc]
      rw [← movingCompensationValues_product]
    have hL := ihL t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1 p XL
    have hR := ihR t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2 p XR
    change (if (p : ZMod q) = 0 then 0 else
      movingSlotSpectator value g D L p XL * star (movingSlotSpectator value g D R p XR)) = _
    rw [hL, hR]
    simp only [buildMovingGiantTree, MovingSampleSlots.values, movingSlotValues,
      movingGiantAmplitude, MovingGiantTree.castConstant_frequency,
      buildMovingGiantTree_frequency, MovingGiantTree.castConstant_amplitude]
    rw [← hp]
    dsimp only [u]
    rw [movingSlotValues_append, movingSlotValues_append, movingCompensationValues_product]
    rfl

end Ostmann

end OAI
