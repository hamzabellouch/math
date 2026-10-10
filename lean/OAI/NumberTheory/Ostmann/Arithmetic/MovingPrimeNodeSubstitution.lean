import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeNodeTransfer
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantIntervalBridge

namespace OAI

/-! # Exact identification of the coefficient node with integer substitution -/

namespace Ostmann
open scoped Classical BigOperators

/-- Every nonzero original node factor comes from the unique positive integer
substitution in its cutoff range. -/
theorem movingPrimeNodeFactor_valid {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (CL CR u : List σ)
    (XL XR : ℕ) (s v w : ℤ) (I : Finset ℕ)
    (hI : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hf : movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR u XL XR s v w ≠ 0) :
    validTransferredPivot I
      (v * (XR * MovingSlotReversal.naturalProduct value CR : ℕ) -
        w * (XL * MovingSlotReversal.naturalProduct value CL : ℕ))
      (s * MovingSlotReversal.naturalProduct value u) := by
  let U := MovingSlotReversal.naturalProduct value u
  let p := movingTopPivot value CL CR u XL XR s v w
  unfold movingPrimeNodeFactor at hf
  dsimp only at hf
  split_ifs at hf with hguard
  · rcases hguard with ⟨_, hnode, hU⟩
    rcases hnode with ⟨hs, _, hrel, hpU, _, _, _, _, _⟩
    change (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) ≠ 0 at hf
    have hp : 0 < p := Nat.pos_of_mul_pos_right hpU
    have hφ : φ (Real.log p - G (n + 1)) ≠ 0 := by
      intro hz
      exact hf (by simp only [hz, mul_zero, Complex.ofReal_zero])
    apply validTransferredPivot_of_eq I _ _ (mul_ne_zero hs (by exact_mod_cast hU.ne'))
      p hp (hI p hp hφ)
    change _ = (s * (U : ℤ)) * (p : ℤ)
    calc
      _ = s * (p * U : ℕ) := hrel
      _ = _ := by rw [Nat.cast_mul]; ring
  · exact (hf rfl).elim

/-- For the concrete giant cell, the original node's support gives exactly
its integer pivot range; endpoint primes and integers are retained. -/
theorem movingPrimeNodeFactor_valid_cell {σ : Type*}
    (value : σ → ℕ) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (φ : ℝ → ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ)
    (n : ℕ) (CL CR u : List σ) (XL XR : ℕ) (s v w : ℤ)
    (hf : movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR u XL XR s v w ≠ 0) :
    validTransferredPivot
      (Finset.Ioc ⌊Real.exp (G (n + 1) - 1)⌋₊ ⌊Real.exp (G (n + 1) + 1)⌋₊)
      (v * (XR * MovingSlotReversal.naturalProduct value CR : ℕ) -
        w * (XL * MovingSlotReversal.naturalProduct value CL : ℕ))
      (s * MovingSlotReversal.naturalProduct value u) :=
  movingPrimeNodeFactor_valid value outside childBound pivotBound φ G n CL CR u XL XR s v w _
    (fun p hp hφ => smoothGiant_nonzero_in_log_cell φ (G (n + 1)) hout p hp hφ) hf

/-- The new coefficient term is exactly the off-diagonal integer-substitution
term from the full transform transfer, with its original two child factors. -/
theorem movingPrimeNodeFactor_substitution {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ)
    (u : TreeLeafTuple (List σ) n) (small bulk : TreeLeafTuple (List σ) (n + 1))
    (XL XR : ℕ) (s v w : ℤ) (I : Finset ℕ)
    (hI : ∀ p ∈ I, 0 < p)
    (hφ : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hsV : s.natAbs ≤ V (n + 1))
    (hv : v.natAbs ≤ childBound (n + 1)) (hw : w.natAbs ≤ childBound (n + 1)) :
    let U := MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)
    let CL := flattenMovingSlots n small.1 ++ flattenMovingSlots n bulk.1
    let CR := flattenMovingSlots n small.2 ++ flattenMovingSlots n bulk.2
    let LH := XL * MovingSlotReversal.naturalProduct value CL
    let RH := XR * MovingSlotReversal.naturalProduct value CR
    let p := movingTopPivot value CL CR (flattenMovingSlots n u) XL XR s v w
    let A := movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n v
      (appendMovingSlotLeaves n u small.1) bulk.1 p XL
    let B := movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n w
      (appendMovingSlotLeaves n u small.2) bulk.2 p XR
    (∀ p ∈ I, p * U ≤ pivotBound (n + 1)) →
    2 * pivotBound (n + 1) * childBound (n + 1) < RH →
    (∀ q, q.Prime → q ∣ RH → V (n + 1) < q) →
    (∀ q, q.Prime → q ∣ U → childBound (n + 1) < q) →
    movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR
      (flattenMovingSlots n u) XL XR s v w * A * star B =
      if validTransferredPivot I (v * RH - w * LH) (s * U) then
        (((U : ℝ) * φ (Real.log p - G (n + 1)) : ℝ) : ℂ) * A * star B else 0 := by
  intro U CL CR LH RH p A B hbound hgap hRH hU
  by_cases h : validTransferredPivot I (v * RH - w * LH) (s * U)
  · rw [ite_eq_left h]
    exact movingPrimeNodeFactor_transfer_product value outside μ childBound pivotBound V F hF φ G n
      u small bulk XL XR s v w I hI hsV hv hw h hbound hgap hRH hU
  · rw [ite_eq_right h]
    have hz : movingPrimeNodeFactor value outside childBound pivotBound φ G n CL CR
        (flattenMovingSlots n u) XL XR s v w = 0 := by
      by_contra hf
      exact h (movingPrimeNodeFactor_valid value outside childBound pivotBound φ G n CL CR
        (flattenMovingSlots n u) XL XR s v w I hφ hf)
    rw [hz, zero_mul, zero_mul]

end Ostmann

end OAI
