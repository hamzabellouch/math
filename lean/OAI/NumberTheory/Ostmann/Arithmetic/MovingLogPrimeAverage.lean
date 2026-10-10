import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkLogWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeFrequencyAverage

namespace OAI

/-! # Terminal log weights through the two giant Page averages -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

section
variable {σ : Type*} (value tier : σ → ℕ) (k : ℕ)
  (outside : List ℕ) (cb cd : ℝ)
  (F : Bool → {d : ℕ} → MovingSlotData σ d → ℤ → ℂ)
  (E : Bool → {d : ℕ} → MovingSlotData σ d → ℤ → ℤ → ℤ → ℝ)
  {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode) (R : ℤ)

theorem movingFrequencyPairFactor_bulk_log (x y : ℤ) :
    movingFrequencyPairFactor value outside
      (fun b {_} T s => (movingBulkLeafLogWeight value tier k outside cb cd T : ℂ) * F b T s)
      E T nodes R x y =
    ((movingBulkTreeLogWeight value tier k outside cb cd (T false) : ℂ) *
      star (movingBulkTreeLogWeight value tier k outside cb cd (T true) : ℂ)) *
      movingFrequencyPairFactor value outside F E T nodes R x y := by
  unfold movingFrequencyPairFactor
  split_ifs
  · rw [movingDataWeight_bulk_log, movingDataWeight_bulk_log]
    simp only [map_mul, Complex.star_def]
    ring
  · exact (mul_zero _).symm

/-- Both Page corrections are unchanged. The original logarithmic weights
are constants only with respect to the two giant residue variables. -/
theorem movingFrequencyPrimeAverage_bulk_log (r : ℕ) [NeZero r]
    (P : PublishedProgressionInput) (Q : ℕ) (x y : ℝ) :
    movingFrequencyPrimeAverage value outside
      (fun b {_} T s => (movingBulkLeafLogWeight value tier k outside cb cd T : ℂ) * F b T s)
      E T nodes R r P Q x y =
    ((movingBulkTreeLogWeight value tier k outside cb cd (T false) : ℂ) *
      star (movingBulkTreeLogWeight value tier k outside cb cd (T true) : ℂ)) *
      movingFrequencyPrimeAverage value outside F E T nodes R r P Q x y := by
  unfold movingFrequencyPrimeAverage
  simp_rw [movingFrequencyPairFactor_bulk_log]
  unfold correctedPrimePairAverage
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

end
end Ostmann

end OAI
