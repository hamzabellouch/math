import OAI.NumberTheory.EgyptianFractions.SelbergWeightBound
import OAI.NumberTheory.EgyptianFractions.SelbergErrorBound
import OAI.NumberTheory.EgyptianFractions.DivisorTupleBounds

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace Problem337.SelbergOptimal

/-- The actual optimal weights have a logarithmically bounded weighted mass.
This uses the sharp coefficient bound, not the crude inverse-density estimate. -/
theorem optimalWeight_primeFactor_mass_le (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ s.prodPrimes.divisors, |optimalWeight s z d| *
      (2 : ℝ) ^ d.primeFactors.card) ≤ (z : ℝ) * (1 + Real.log z) ^ 2 := by
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors,
        if d ≤ z then (2 : ℝ) ^ d.primeFactors.card else 0 := by
      apply sum_le_sum
      intro d hd
      by_cases hdz : d ≤ z
      · rw [ite_eq_left hdz]
        have hw : |optimalWeight s z d| ≤ 1 := by
          rw [optimalWeight_formula s z d (Nat.dvd_of_mem_divisors hd)]
          convert abs_normalized_complement_le_one s hz (Nat.dvd_of_mem_divisors hd) using 1
          unfold complementNormalizer
          congr 1
          ring
        simpa using mul_le_mul_of_nonneg_right hw
          (by positivity : 0 ≤ (2 : ℝ) ^ d.primeFactors.card)
      · rw [ite_eq_right hdz, optimalWeight_eq_zero_of_lt s (lt_of_not_ge hdz)]
        simp
    _ = ∑ d ∈ s.prodPrimes.divisors.filter (fun d => d ≤ z),
        (2 : ℝ) ^ d.primeFactors.card := (sum_filter _ _).symm
    _ ≤ _ := SelbergError.sum_squarefree_pow_le _ 2 z
      (fun d hd => s.squarefree_of_mem_divisors_prodPrimes (mem_filter.mp hd).1)
      (by
        intro d hd
        obtain ⟨hdP, hdz⟩ := mem_filter.mp hd
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, hdz⟩)

/-- A dimension-two local remainder envelope gives an explicit logarithmic
error for the constructed optimal Selberg weights. -/
theorem errSum_optimalWeight_le_log (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤
        (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card) :
    s.errSum (BoundingSieve.lambdaSquared (optimalWeight s z)) ≤
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 := by
  calc
    _ ≤ (∑ d ∈ s.prodPrimes.divisors, |optimalWeight s z d| *
        (2 : ℝ) ^ d.primeFactors.card) ^ 2 :=
      SelbergError.errSum_lambdaSquared_le_sq s (optimalWeight s z)
        (fun d => (2 : ℝ) ^ d.primeFactors.card) hrem
    _ ≤ ((z : ℝ) * (1 + Real.log z) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sum_nonneg (by intros; positivity))
        (optimalWeight_primeFactor_mass_le s hz) 2
    _ = _ := by ring

/-- Fully optimized finite Selberg inequality with explicit logarithmic error. -/
theorem siftedSum_le_log_error (s : BoundingSieve) {z : ℕ} (hz : 1 ≤ z)
    (hrem : ∀ a ∈ s.prodPrimes.divisors, ∀ b ∈ s.prodPrimes.divisors,
      |s.rem (Nat.lcm a b)| ≤
        (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card) :
    s.siftedSum ≤ s.totalMass / normalizer s z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 :=
  (siftedSum_le s hz).trans
    (add_le_add le_rfl (errSum_optimalWeight_le_log s hz hrem))

end Problem337.SelbergOptimal

end

end OAI
