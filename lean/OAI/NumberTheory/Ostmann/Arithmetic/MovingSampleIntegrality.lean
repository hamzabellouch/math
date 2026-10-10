import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleValues

namespace OAI

/-! # Full integer support for the labelled moving-giant sampler -/

namespace Ostmann
open scoped Classical

@[simp] theorem MovingGiantTree.castConstant_integral {n C D : ℕ} (h : C = D)
    (T : MovingGiantTree n C) (XL XR : ℕ) (bulk : TreeLeafTuple ℕ n) :
    (T.castConstant h).Integral XL XR bulk ↔ T.Integral XL XR bulk := by
  subst D
  rfl

/-- The labelled history is interpreted by the same positive integer pivots
as the original sampler. No primality is imposed on a reconstructed giant. -/
def MovingSlotData.Integral {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, .leaf _ _, _, _ => True
  | _, .node s CL CR u left right, XL, XR =>
      let step := MovingSlotData.step s CL CR u left right false
      let p := step.naturalPivot value XL XR
      step.IntegralAt value (XL, XR) ∧ left.Integral value p XL ∧ right.Integral value p XR

theorem buildMovingSlotData_integral {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (XL XR : ℕ) :
    (buildMovingSlotData n t small bulk samples).Integral value XL XR ↔
      (buildMovingGiantTree n t (movingSlotValues value n small) (samples.values value)).Integral
        XL XR (movingSlotValues value n bulk) := by
  induction samples generalizing XL XR with
  | leaf => rfl
  | @node n samples left right ihL ihR =>
    let u := movingCompensationSlots n samples
    let comp := treeLeafProduct n (movingSlotValues value n u)
    let CL := treeLeafProduct n (movingSlotValues value n small.1)
    let CR := treeLeafProduct n (movingSlotValues value n small.2)
    let ML := treeLeafProduct n (movingSlotValues value n bulk.1)
    let MR := treeLeafProduct n (movingSlotValues value n bulk.2)
    let step := MovingSlotData.step t.1
      (flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1)
      (flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2)
      (flattenMovingSlots n u)
      (buildMovingSlotData n t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1 left)
      (buildMovingSlotData n t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2 right) false
    have hp : step.naturalPivot value XL XR =
        movingGiantPivot t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
          CL CR comp XL XR ML MR := by
      simp only [MovingSlotReversal.naturalPivot, step, MovingSlotData.step,
        buildMovingSlotData_frequency, movingNaturalProduct_append, movingSlotValues_flatten]
      simp only [movingGiantPivot, CL, CR, ML, MR, comp, Nat.mul_one, Nat.mul_assoc]
    have hL := ihL t.2.1 (appendMovingSlotLeaves n u small.1) bulk.1
      (step.naturalPivot value XL XR) XL
    have hR := ihR t.2.2 (appendMovingSlotLeaves n u small.2) bulk.2
      (step.naturalPivot value XL XR) XR
    change (step.IntegralAt value (XL, XR) ∧ _ ∧ _) ↔ _
    rw [hL, hR]
    simp only [buildMovingGiantTree, MovingSampleSlots.values, movingSlotValues,
      MovingGiantTree.Integral, MovingGiantTree.castConstant_frequency,
      buildMovingGiantTree_frequency, MovingGiantTree.castConstant_integral]
    simp only [← movingCompensationValues_product, hp]
    have hstep : step.IntegralAt value (XL, XR) ↔
        0 < step.naturalPivot value XL XR ∧
          frequencyRoot n t.2.1 * ((XR * CR * MR : ℕ) : ℤ) -
            frequencyRoot n t.2.2 * ((XL * CL * ML : ℕ) : ℤ) =
              t.1 * ((comp * step.naturalPivot value XL XR : ℕ) : ℤ) := by
      simp only [MovingSlotReversal.IntegralAt, step, MovingSlotData.step,
        buildMovingSlotData_frequency, movingNaturalProduct_append, movingSlotValues_flatten]
      dsimp only [CL, CR, ML, MR, comp]
      simp only [Nat.mul_assoc]
    rw [hstep]
    simp only [hp]
    simp only [CL, CR, ML, MR, comp, u, and_assoc]
    rw [movingSlotValues_append, movingSlotValues_append, movingCompensationValues_product]

end Ostmann

end OAI
