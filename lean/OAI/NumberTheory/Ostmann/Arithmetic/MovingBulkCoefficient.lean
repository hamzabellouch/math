import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkRecursiveWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyCoefficient

namespace OAI

/-! # External bulk weights in the exact original coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingSupportedSampleTerm_bulk_log {σ : Type*}
    (value tier : σ → ℕ) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) (a : MovingSampleSlots σ n) :
    movingSupportedSampleTerm value outside childBound pivotBound
        (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
        E n t small bulk XL XR a =
      (movingBulkTreeLogWeight value tier k outside cb cd
        (buildMovingSlotData n t small bulk a) : ℂ) *
        movingSupportedSampleTerm value outside childBound pivotBound F E n t small bulk XL XR a := by
  unfold movingSupportedSampleTerm
  rw [movingSlotWeight_bulk_log]
  unfold movingSupportedWeight
  split_ifs
  · rfl
  · exact (mul_zero _).symm

/-- Extracting the logarithmic weights does not restrict the independent
compensation prior. Its zero terms vanish; every remaining draw has the
prescribed tier and therefore gives the same external bulk factor. -/
theorem movingSupportedSampledWeight_bulk_log {σ : Type} [Fintype σ]
    (value tier : σ → ℕ) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    (μ : ℕ → σ → ℝ) (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (hn : n ≤ k) (hsmall : ∀ i ∈ flattenMovingSlots n small, tier i ≠ k)
    (hbulk : ∀ i ∈ flattenMovingSlots n bulk, tier i = k) (XL XR : ℕ) :
    movingSupportedSampledWeight value outside μ childBound pivotBound
        (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
        E n t small bulk XL XR =
      ((treeLeafProduct n (treeLeafMap (movingBulkListLogWeight value outside cb cd) n bulk) : ℝ) : ℂ) *
        movingSupportedSampledWeight value outside μ childBound pivotBound F E n t small bulk XL XR := by
  rw [movingSupportedSampledWeight_eq, movingSupportedSampledWeight_eq]
  unfold movingCompensatedAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : movingSamplesPrior μ a = 0
  · simp only [ha, mul_zero, Complex.ofReal_zero, zero_mul, mul_zero]
  · rw [movingSupportedSampleTerm_bulk_log,
      movingBulkTreeLogWeight_sample value tier k outside cb cd n t small bulk a hn
        hsmall hbulk (movingSamplesPrior_levels μ tier hμ a ha)]
    ring

theorem movingFrequencyCoefficient_bulk_log {σ : Type} [Fintype σ]
    (value tier : σ → ℕ) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    (μ : ℕ → σ → ℝ) (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (small bulk : TreeLeafTuple (List σ) n)
    (hn : n ≤ k) (hsmall : ∀ i ∈ flattenMovingSlots n small, tier i ≠ k)
    (hbulk : ∀ i ∈ flattenMovingSlots n bulk, tier i = k) (XL XR : ℕ) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
        (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
        φ G n s small bulk XL XR =
      ((treeLeafProduct n (treeLeafMap (movingBulkListLogWeight value outside cb cd) n bulk) : ℝ) : ℂ) *
        movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s small bulk XL XR := by
  unfold movingFrequencyCoefficient
  simp only [movingSupportedSampledWeight_bulk_log value tier k outside cb cd μ hμ
    childBound pivotBound F _ n _ small bulk hn hsmall hbulk XL XR, Finset.mul_sum]

end Ostmann

end OAI
