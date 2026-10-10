import OAI.NumberTheory.EgyptianFractions.RoughPart
import OAI.NumberTheory.EgyptianFractions.RoughDivisorAsymptotic

namespace OAI
noncomputable section
open Filter

namespace Problem337

/-- Uniform subpower bound for rough divisors of an arbitrary positive integer.
The ambient integer may have small prime factors. The threshold and the finite
family may both vary after the single eventual size threshold is chosen. -/
theorem eventually_rough_divisor_card_subpower
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ n : ℕ, n ≠ 0 →
      Real.log (n : ℝ) ≤ A * Real.log X * Real.log (Real.log X) →
      ∀ R : ℝ, Real.log X ≤ R → ∀ s : Finset ℕ,
      (∀ d ∈ s, d ∣ n) → (∀ d ∈ s, (d : ℝ) ≤ X) →
      (∀ d ∈ s, ∀ p ∈ d.primeFactorsList, R ≤ (p : ℝ)) →
      (s.card : ℝ) ≤ X ^ ε := by
  filter_upwards [eventually_truncatedDivisorCount_rough_subpower A ε hA hε]
    with X hX
  intro n hn hsize R hR s hdiv hsmall hrough
  have hcount := hX (roughPart R n) (roughPart_pos R n).ne'
    ((roughPart_log_le R hn).trans hsize)
    (fun p hp => hR.trans (roughPart_large R n p hp))
  exact (show (s.card : ℝ) ≤ truncatedDivisorCount X (roughPart R n) by
    exact_mod_cast rough_divisor_card_le_truncated_roughPart R X hn s
      hdiv hsmall hrough).trans hcount

/-- The literal filtered-divisor-set version of the preceding uniform bound. -/
theorem eventually_card_rough_divisors_subpower
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ n : ℕ, n ≠ 0 →
      Real.log (n : ℝ) ≤ A * Real.log X * Real.log (Real.log X) →
      ∀ R : ℝ, Real.log X ≤ R →
      ((n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X ∧
        ∀ p ∈ d.primeFactorsList, R ≤ (p : ℝ))).card : ℝ) ≤ X ^ ε := by
  classical
  filter_upwards [eventually_rough_divisor_card_subpower A ε hA hε] with X hX
  intro n hn hsize R hR
  apply hX n hn hsize R hR
  · intro d hd
    exact Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  · intro d hd
    exact (Finset.mem_filter.mp hd).2.1
  · intro d hd
    exact (Finset.mem_filter.mp hd).2.2

end Problem337

end

end OAI
