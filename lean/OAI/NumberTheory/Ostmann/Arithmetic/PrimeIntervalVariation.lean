import Mathlib.Algebra.BigOperators.Intervals
import OAI.NumberTheory.Ostmann.ZeroDensity.UniformPrimeProgressions
import OAI.NumberTheory.Ostmann.Characters.WeightedPhaseExtraction

namespace OAI

/-! # Weighted short prime intervals from the published progression input -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem reciprocalPrimeInterval_add (q a : ℕ) (u v w : ℝ) (huv : u ≤ v) (hvw : v ≤ w) :
    reciprocalPrimeInterval q a u v + reciprocalPrimeInterval q a v w =
      reciprocalPrimeInterval q a u w := by
  exact Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor huv) (Nat.floor_le_floor hvw)

theorem primeLogDensity_integral_add (φ χ β u v w : ℝ) (hu : 0 < u) (huv : u ≤ v) (hvw : v ≤ w) :
    (∫ y in Set.Ioc u v, primeLogDensity φ χ β y) +
      (∫ y in Set.Ioc v w, primeLogDensity φ χ β y) =
        ∫ y in Set.Ioc u w, primeLogDensity φ χ β y := by
  rw [← intervalIntegral.integral_of_le huv, ← intervalIntegral.integral_of_le hvw,
    ← intervalIntegral.integral_of_le (huv.trans hvw)]
  exact intervalIntegral.integral_add_adjacent_intervals
    ((continuousOn_primeLogDensity φ χ β hu).intervalIntegrable_of_Icc huv)
    ((continuousOn_primeLogDensity φ χ β (hu.trans_le huv)).intervalIntegrable_of_Icc hvw)

/-- The reference density is the actual selected Page-corrected density.
It stays inside the integral throughout weighted summation. -/
noncomputable def selectedPrimeLogDensity (P : PublishedProgressionInput) (Q q a : ℕ) : ℝ → ℝ :=
  primeLogDensity (Nat.totient q)
    (pageCoefficient (pageAtModulus q (selectedPageZero P Q)) a)
    (pageBeta (pageAtModulus q (selectedPageZero P Q)))

/-- Finite Abel summation turns the uniform interval error into a variation
error for the actual complex weights. There is no factor for the number of
partition intervals. -/
theorem PublishedProgressionInput.weighted_prime_interval_variation
    (P : PublishedProgressionInput) {Q q a : ℕ}
    (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (s : ℕ → ℝ) (hs : Monotone s) (hs0 : 1 ≤ s 0) (N : ℕ) (hshort : s N ≤ s 0 + 1)
    (w : ℕ → ℂ) :
    ‖∑ j ∈ Finset.range N, w j *
      ((reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1))) -
        ∫ y in Set.Ioc (s j) (s (j + 1)), selectedPrimeLogDensity P Q q a y : ℝ) : ℂ)‖ ≤
      discreteVariation w N *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s 0)) +
          Real.exp (-P.kappa * s 0 / Real.log (4 * (Q : ℝ)))) := by
  let E : ℝ → ℝ := fun t => reciprocalPrimeInterval q a (Real.exp (s 0)) (Real.exp t) -
    ∫ y in Set.Ioc (s 0) t, selectedPrimeLogDensity P Q q a y
  have hzero : E (s 0) = 0 := by simp [E, reciprocalPrimeInterval]
  have hstep (j : ℕ) :
      reciprocalPrimeInterval q a (Real.exp (s j)) (Real.exp (s (j + 1))) -
        (∫ y in Set.Ioc (s j) (s (j + 1)), selectedPrimeLogDensity P Q q a y) =
          E (s (j + 1)) - E (s j) := by
    have hp := reciprocalPrimeInterval_add q a (Real.exp (s 0)) (Real.exp (s j))
      (Real.exp (s (j + 1))) (Real.exp_le_exp.mpr (hs (Nat.zero_le _)))
      (Real.exp_le_exp.mpr (hs (Nat.le_succ _)))
    have hi := primeLogDensity_integral_add (Nat.totient q)
      (pageCoefficient (pageAtModulus q (selectedPageZero P Q)) a)
      (pageBeta (pageAtModulus q (selectedPageZero P Q))) (s 0) (s j) (s (j + 1))
      (by linarith) (hs (Nat.zero_le _)) (hs (Nat.le_succ _))
    change (∫ y in Set.Ioc (s 0) (s j), selectedPrimeLogDensity P Q q a y) +
      (∫ y in Set.Ioc (s j) (s (j + 1)), selectedPrimeLogDensity P Q q a y) =
        (∫ y in Set.Ioc (s 0) (s (j + 1)), selectedPrimeLogDensity P Q q a y) at hi
    dsimp only [E]
    linarith
  have hprefix (k : ℕ) (hk : k ≤ N) :
      ‖∑ j ∈ Finset.range k, ((E (s (j + 1)) - E (s j) : ℝ) : ℂ)‖ ≤
        18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s 0)) +
          Real.exp (-P.kappa * s 0 / Real.log (4 * (Q : ℝ))) := by
    rw [← Complex.ofReal_sum, Finset.sum_range_sub (fun j => E (s j)), hzero, sub_zero,
      Complex.norm_real, Real.norm_eq_abs]
    exact P.uniform_log_interval hQ hq hqQ ha hs0 (hs (Nat.zero_le k))
      ((hs hk).trans hshort)
  simp_rw [hstep]
  exact weighted_sum_le_variation w _ N _ hprefix

end Ostmann

end OAI
