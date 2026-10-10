import OAI.NumberTheory.Ostmann.Arithmetic.MovingRootReconstruction

namespace OAI

/-! # The original sampled recursion with the explicit giant quotient -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original sample law and the two independent child sample trees are
retained. The inserted giant is exactly `(v H⁻ - w H⁺)/(s U)`, matching the
weighted integer off-diagonal, with every root support test still explicit. -/
theorem movingSampledWeight_direct_node {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ (n + 1))
    (small bulk : TreeLeafTuple (List σ) (n + 1)) (XL XR : ℕ) :
    let E := movingCompensatedExtra value (movingOriginalNode value childBound pivotBound φ G)
    movingSampledWeight value μ childBound pivotBound F E (n + 1) t small bulk XL XR =
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
          if ValidTransferNode (movingSlotSystem value childBound pivotBound) x t.1 v w (p * U) ∧
              0 < U then
            (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) *
              movingSampledWeight value μ childBound pivotBound F E n t.2.1
                (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
              star (movingSampledWeight value μ childBound pivotBound F E n t.2.2
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
  have hroot := movingSampleRootFactor_reconstructed value childBound pivotBound φ G n t
    CL CR (flattenMovingSlots n u) XL XR
  dsimp only at hroot
  simp only [← Complex.ofReal_mul] at hroot
  change movingSampleRootFactor value childBound pivotBound E n t CL CR
      (flattenMovingSlots n u) XL XR =
    if ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U then
      (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) else 0 at hroot
  change (movingCompensationPrior (μ n) n a : ℂ) *
      movingSampleRootFactor value childBound pivotBound E n t CL CR
        (flattenMovingSlots n u) XL XR *
      movingSampledWeight value μ childBound pivotBound F E n t.2.1
        (appendMovingSlotLeaves n u small.1) bulk.1 (P / U) XL *
      star (movingSampledWeight value μ childBound pivotBound F E n t.2.2
        (appendMovingSlotLeaves n u small.2) bulk.2 (P / U) XR) =
    (movingCompensationPrior (μ n) n a : ℂ) *
      (if ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U then
        (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) *
          movingSampledWeight value μ childBound pivotBound F E n t.2.1
            (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
          star (movingSampledWeight value μ childBound pivotBound F E n t.2.2
            (appendMovingSlotLeaves n u small.2) bulk.2 p XR)
        else 0)
  rw [hroot]
  by_cases h : ValidTransferNode sys x t.1 v w (p * U) ∧ 0 < U
  · have hP : P = p * U := h.1.historyPivot_eq
    have hp : P / U = p := by rw [hP, Nat.mul_div_left _ h.2]
    rw [ite_eq_left h, ite_eq_left h, hp]
    ring
  · rw [ite_eq_right h, ite_eq_right h]
    simp only [mul_zero, zero_mul]

end Ostmann

end OAI
