import OAI.NumberTheory.Ostmann.Construction.InitialMovingRecursiveWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyCoefficient

namespace OAI

/-! # Exact half-bulk factorization under the unchanged compensation law -/
namespace Ostmann
open scoped Classical BigOperators

theorem movingSupportedSampleTerm_initial_halves {P : Type}
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (E : MovingSlotState P → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List P) n)
    (XL XR : ℕ) (a : MovingSampleSlots P n) :
    movingSupportedSampleTerm value outside childBound pivotBound
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      E n t small bulk XL XR a =
    (initialMovingTreeWeight value b d r cb cd sl sr fallback
      (buildMovingSlotData n t small bulk a) : ℂ) *
      movingSupportedSampleTerm value outside childBound pivotBound F E n t small bulk XL XR a := by
  unfold movingSupportedSampleTerm
  rw [movingSlotWeight_initial_halves]
  unfold movingSupportedWeight
  split_ifs
  · rfl
  · exact (mul_zero _).symm

theorem movingSupportedSampledWeight_initial_halves {P : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (E : MovingSlotState P → ℤ → ℤ → ℤ → ℝ)
    (n s : ℕ) (t : FrequencyTree ℤ n) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small s) (hlen : s + 4 * n = r + r)
    (XL XR : ℕ) :
    movingSupportedSampledWeight value outside μ childBound pivotBound
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      E n t small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingSupportedSampledWeight value outside μ childBound pivotBound F E n t small
        (bulkSlotLeaves n (b + b) slot) XL XR := by
  rw [movingSupportedSampledWeight_eq, movingSupportedSampledWeight_eq]
  unfold movingCompensatedAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [movingSupportedSampleTerm_initial_halves,
    initialMovingTreeWeight_sample value b d r cb cd sl sr fallback n s t small slot a hsmall hlen]
  ring

theorem movingFrequencyCoefficient_initial_halves {P : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState P → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n a : ℕ) (s : ℤ) (small : TreeLeafTuple (List P) n)
    (slot : TreeLeafIndex n × Fin (b + b) → P)
    (hsmall : MovingLeafLengthEq n small a) (hlen : a + 4 * n = r + r)
    (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
      φ G n s small (bulkSlotLeaves n (b + b) slot) XL XR =
    (initialHalfBulkProduct value b d cb cd sl sr n slot : ℂ) *
      movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s small
        (bulkSlotLeaves n (b + b) slot) XL XR := by
  unfold movingFrequencyCoefficient
  simp only [movingSupportedSampledWeight_initial_halves value b d r cb cd sl sr fallback
    outside μ childBound pivotBound F _ n a _ small slot hsmall hlen XL XR, Finset.mul_sum]

end Ostmann

end OAI
