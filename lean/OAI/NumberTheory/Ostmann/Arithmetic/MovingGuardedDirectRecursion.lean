import OAI.NumberTheory.Ostmann.Arithmetic.MovingDirectRecursion

namespace OAI

/-! # The fully guarded sampled recursion with the explicit giant quotient -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original sample law and the two independent child sample trees are
retained. The inserted giant is exactly `(v H⁻ - w H⁺)/(s U)`, matching the
weighted integer off-diagonal, with every root support test still explicit. -/
theorem movingSampledWeight_guarded_direct_node {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (small bulk : TreeLeafTuple (List σ) (n + 1)) (XL XR : ℕ) :
    let E := movingCompensatedExtra value (movingOriginalNode value childBound pivotBound φ G)
    movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F) (movingGuardedExtra value outside E) (n + 1) t small bulk XL XR =
      ∑ a : TreeLeafTuple (Fin 4 → σ) n,
        let u := movingCompensationSlots n a
        let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
        let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
        let x := movingRootState n t CL CR (flattenMovingSlots n u) XL XR
        let U := x.compensation value
        let v := frequencyRoot n t.2.1
        let w := frequencyRoot n t.2.2
        let p := reconstructedPivot
          (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ)) (t.1 * U)
        (movingCompensationPrior (μ n) n a : ℂ) *
          if movingLocalSupport value outside x ∧
              (ValidTransferNode (movingSlotSystem value childBound pivotBound) x t.1 v w (p * U) ∧
                0 < U) then
            (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) *
              movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F) (movingGuardedExtra value outside E) n t.2.1
                (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
              star (movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F) (movingGuardedExtra value outside E) n t.2.2
                (appendMovingSlotLeaves n u small.2) bulk.2 p XR)
          else 0 := by
  intro E
  rw [movingSampledWeight_node]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  let u := movingCompensationSlots n a
  let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
  let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
  let x := movingRootState n t CL CR (flattenMovingSlots n u) XL XR
  let U := x.compensation value
  let sys := movingSlotSystem value childBound pivotBound
  let v := frequencyRoot n t.2.1
  let w := frequencyRoot n t.2.2
  let P := historyPivot sys x t.1 v w
  let p := reconstructedPivot (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ)) (t.1 * U)
  have hbase := movingSampleRootFactor_reconstructed value childBound pivotBound φ G n t
    CL CR (flattenMovingSlots n u) XL XR
  dsimp only at hbase
  simp only [← Complex.ofReal_mul] at hbase
  have hguard := movingSampleRootFactor_guarded value outside childBound pivotBound E n t
    CL CR (flattenMovingSlots n u) XL XR
  rw [hbase] at hguard
  change movingSampleRootFactor value childBound pivotBound
      (movingGuardedExtra value outside E) n t CL CR (flattenMovingSlots n u) XL XR =
    (if movingLocalSupport value outside x then
      (if ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U then
        (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) else 0) else 0) at hguard
  have hroot : movingSampleRootFactor value childBound pivotBound
      (movingGuardedExtra value outside E) n t CL CR (flattenMovingSlots n u) XL XR =
      if movingLocalSupport value outside x ∧
          (ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U) then
        (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) else 0 := by
    rw [hguard]
    by_cases hl : movingLocalSupport value outside x
    · simp only [hl, true_and, ite_true]
    · simp only [hl, false_and, ite_false]
  change (movingCompensationPrior (μ n) n a : ℂ) *
      movingSampleRootFactor value childBound pivotBound (movingGuardedExtra value outside E) n t CL CR
        (flattenMovingSlots n u) XL XR *
      movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F) (movingGuardedExtra value outside E) n t.2.1
        (appendMovingSlotLeaves n u small.1) bulk.1 (P / U) XL *
      star (movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F) (movingGuardedExtra value outside E) n t.2.2
        (appendMovingSlotLeaves n u small.2) bulk.2 (P / U) XR) =
    (movingCompensationPrior (μ n) n a : ℂ) *
      (if movingLocalSupport value outside x ∧
          (ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U) then
        (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) *
          movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F) (movingGuardedExtra value outside E) n t.2.1
            (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
          star (movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F) (movingGuardedExtra value outside E) n t.2.2
            (appendMovingSlotLeaves n u small.2) bulk.2 p XR)
        else 0)
  rw [hroot]
  by_cases h : movingLocalSupport value outside x ∧
      (ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U)
  · have hP : P = p * U := h.2.1.historyPivot_eq
    have hp : P / U = p := by rw [hP, Nat.mul_div_left _ h.2.2]
    rw [ite_eq_left h, ite_eq_left h, hp]
    ring
  · rw [ite_eq_right h, ite_eq_right h]
    simp only [mul_zero, zero_mul]

/-- The same exact recurrence for the fully supported coefficient used by
the arithmetic comparison. -/
theorem movingSupportedSampledWeight_direct_node {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (small bulk : TreeLeafTuple (List σ) (n + 1)) (XL XR : ℕ) :
    let E := movingOriginalNode value childBound pivotBound φ G
    movingSupportedSampledWeight value outside μ childBound pivotBound F E (n + 1) t small bulk XL XR =
      ∑ a : TreeLeafTuple (Fin 4 → σ) n,
        let u := movingCompensationSlots n a
        let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
        let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
        let x := movingRootState n t CL CR (flattenMovingSlots n u) XL XR
        let U := x.compensation value
        let v := frequencyRoot n t.2.1
        let w := frequencyRoot n t.2.2
        let p := reconstructedPivot
          (v * (x.rightProduct value : ℤ) - w * (x.leftProduct value : ℤ)) (t.1 * U)
        (movingCompensationPrior (μ n) n a : ℂ) *
          if movingLocalSupport value outside x ∧
              (ValidTransferNode (movingSlotSystem value childBound pivotBound) x t.1 v w (p * U) ∧
                0 < U) then
            (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) *
              movingSupportedSampledWeight value outside μ childBound pivotBound F E n t.2.1
                (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
              star (movingSupportedSampledWeight value outside μ childBound pivotBound F E n t.2.2
                (appendMovingSlotLeaves n u small.2) bulk.2 p XR)
          else 0 := by
  dsimp only
  simpa only [movingSupportedSampledWeight, movingLocalExtra_compensated,
    movingOriginalNode_local] using
    movingSampledWeight_guarded_direct_node value outside μ childBound pivotBound F φ G
      n t small bulk XL XR

end Ostmann

end OAI
