import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeNodeFactor
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRootedSum

namespace OAI

/-! # The complete coefficient recursion at actual top primes -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFrequencyCoefficient_zero {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ)
    (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      n 0 small bulk XL XR = 0 := by
  unfold movingFrequencyCoefficient
  apply Finset.sum_eq_zero
  intro t _
  apply movingSupportedSampledWeight_zero_frequency value outside μ childBound pivotBound
    F _ hF n _ small bulk XL XR
  intro h
  apply h 0
  · cases n with
    | zero => exact List.mem_singleton_self _
    | succ n => exact List.mem_cons_self
  · rfl

/-- At actual prime giants, the original coefficient is the product recursion
in the two complete child coefficients. The shared compensation prior occurs
once, and every child retains its own descendant frequency and prime samples. -/
theorem movingFrequencyCoefficient_prime_node {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (hs : s ≠ 0) (hsV : s.natAbs ≤ V (n + 1))
    (small bulk : TreeLeafTuple (List σ) (n + 1)) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      (n + 1) s small bulk XL XR =
      ∑ a : TreeLeafTuple (Fin 4 → σ) n, (movingCompensationPrior (μ n) n a : ℂ) *
        ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
          let u := movingCompensationSlots n a
          let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
          let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
          let p := movingTopPivot value CL CR (flattenMovingSlots n u) XL XR s v.val w.val
          movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR
              (flattenMovingSlots n u) XL XR s v.val w.val *
            movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n v.val
              (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
            star (movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n w.val
              (appendMovingSlotLeaves n u small.2) bulk.2 p XR) := by
  rw [movingFrequencyCoefficient_node]
  simp_rw [movingPrimeNodeFactor_term value outside μ childBound pivotBound V hV F hF
    φ G n s hs hsV _ _ small bulk _ XL XR hXL hXR hVL hVR]
  conv_lhs =>
    arg 2
    ext l
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [← Finset.mul_sum]
  let u := movingCompensationSlots n a
  let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
  let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
  let P := fun v w : ℤ => movingTopPivot value CL CR (flattenMovingSlots n u) XL XR s v w
  let W := fun v w : ℤ => movingPrimeNodeFactor value outside childBound pivotBound φ G n
    CL CR (flattenMovingSlots n u) XL XR s v w
  let L := fun v w t => movingSupportedSampledWeight value outside μ childBound pivotBound F
    (movingOriginalNode value childBound pivotBound φ G) n t
    (appendMovingSlotLeaves n u small.1) bulk.1 (P v w) XL
  let R := fun v w t => movingSupportedSampledWeight value outside μ childBound pivotBound F
    (movingOriginalNode value childBound pivotBound φ G) n t
    (appendMovingSlotLeaves n u small.2) bulk.2 (P v w) XR
  have h := scheduledFrequency_bilinear_sum V n W L R
  unfold movingFrequencyCoefficient
  apply congrArg (fun z : ℂ => (movingCompensationPrior (μ n) n a : ℂ) * z)
  exact h

end Ostmann

end OAI
