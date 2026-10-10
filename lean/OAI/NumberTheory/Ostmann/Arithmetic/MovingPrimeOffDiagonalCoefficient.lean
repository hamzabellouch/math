import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeNodeSubstitution

namespace OAI

/-! # The complete next coefficient as the original integer off-diagonal -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingPrimeOffDiagonalCoefficient {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (small bulk : TreeLeafTuple (List σ) (n + 1)) (XL XR : ℕ) (I : Finset ℕ) : ℂ :=
  ∑ a : TreeLeafTuple (Fin 4 → σ) n, (movingCompensationPrior (μ n) n a : ℂ) *
    ∑ v : transferFrequencyRange (V n), ∑ w : transferFrequencyRange (V n),
      let u := movingCompensationSlots n a
      let U := MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)
      let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
      let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
      let p := movingTopPivot value CL CR (flattenMovingSlots n u) XL XR s v.val w.val
      if validTransferredPivot I
          (v.val * (XR * MovingSlotReversal.naturalProduct value CR : ℕ) -
            w.val * (XL * MovingSlotReversal.naturalProduct value CL : ℕ)) (s * U) then
        (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) *
          movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n v.val
            (appendMovingSlotLeaves n u small.1) bulk.1 p XL *
          star (movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n w.val
            (appendMovingSlotLeaves n u small.2) bulk.2 p XR)
      else 0

/-- This identifies the full next coefficient, rather than a history-wise
surrogate. Only compensation samples with nonzero original prior need the
range bounds. -/
theorem movingFrequencyCoefficient_eq_offDiagonal {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (hs : s ≠ 0) (hsV : s.natAbs ≤ V (n + 1))
    (small bulk : TreeLeafTuple (List σ) (n + 1)) (XL XR : ℕ)
    (hXL : XL.Prime) (hXR : XR.Prime)
    (hVL : V (n + 1) < XL) (hVR : V (n + 1) < XR)
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1)) :
    let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
    let RH := XR * MovingSlotReversal.naturalProduct value CR
    2 * pivotBound (n + 1) * childBound (n + 1) < RH →
    (∀ q, q.Prime → q ∣ RH → V (n + 1) < q) →
    (∀ a : TreeLeafTuple (Fin 4 → σ) n, movingCompensationPrior (μ n) n a ≠ 0 →
      let U := MovingSlotReversal.naturalProduct value (flattenMovingSlots n (movingCompensationSlots n a))
      (∀ p ∈ I, p * U ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ U → childBound (n + 1) < q)) →
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G (n + 1) s small bulk XL XR =
      movingPrimeOffDiagonalCoefficient value outside μ childBound pivotBound V F φ G n s small bulk XL XR I := by
  intro CR RH hgap hRH hU
  rw [movingFrequencyCoefficient_prime_node value outside μ childBound pivotBound V hV F hF
    φ G n s hs hsV small bulk XL XR hXL hXR hVL hVR]
  unfold movingPrimeOffDiagonalCoefficient
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : movingCompensationPrior (μ n) n a = 0
  · simp only [ha, Complex.ofReal_zero, zero_mul]
  · apply congrArg (fun z : ℂ => (movingCompensationPrior (μ n) n a : ℂ) * z)
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    exact movingPrimeNodeFactor_substitution value outside μ childBound pivotBound V F hF φ G n
      (movingCompensationSlots n a) small bulk XL XR s v.val w.val I hI hφ hsV
      (((mem_transferFrequencyRange _ _).mp v.property).trans hchild)
      (((mem_transferFrequencyRange _ _).mp w.property).trans hchild)
      (hU a ha).1 hgap hRH (hU a ha).2

end Ostmann

end OAI
