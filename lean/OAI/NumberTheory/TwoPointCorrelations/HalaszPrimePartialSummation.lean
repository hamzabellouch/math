import OAI.NumberTheory.TwoPointCorrelations.HalaszPrimeMass
import OAI.NumberTheory.TwoPointCorrelations.PrimePartialSummation

namespace OAI

/-! Partial summation centered at Mertens' logarithmic main term. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def halaszPrimeWeight (n : ℕ) : ℝ :=
  if n.Prime then Real.log (n : ℝ) / n else 0

lemma halasz_prime_weight_prefix (x : ℝ) :
    partialCoefficientSum halaszPrimeWeight x =
      ∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p := by
  have he : Icc 0 ⌊x⌋₊ = Iic ⌊x⌋₊ := by ext n; simp
  simp only [partialCoefficientSum, he, sievePrimesUpTo, halaszPrimeWeight, sum_filter]

lemma halasz_prime_weight_band (f : ℝ → ℝ) {a b : ℝ} :
    (∑ p ∈ mrtPrimeBand a b, f p * (Real.log (p : ℝ) / p)) =
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * halaszPrimeWeight n := by
  have he : mrtPrimeBand a b = (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime := by
    ext n
    simp only [mrtPrimeBand, sievePrimesUpTo, mem_sdiff, mem_filter, mem_Iic, mem_Ioc]
    by_cases hn : n.Prime <;> simp [hn, not_le, and_comm]
  rw [he, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hn : n.Prime <;> simp [halaszPrimeWeight, hn]

theorem halasz_prime_partial_summation (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (f : ℝ → ℝ) (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∑ p ∈ mrtPrimeBand a b, f p * (Real.log (p : ℝ) / p)) -
        (∫ t in a..b, f t / t) =
      f b * (partialCoefficientSum halaszPrimeWeight b - Real.log b) -
      f a * (partialCoefficientSum halaszPrimeWeight a - Real.log a) -
      ∫ t in a..b, deriv f t *
        (partialCoefficientSum halaszPrimeWeight t - Real.log t) := by
  have hxn : ∀ x ∈ Set.Icc a b, x ≠ 0 := fun x hx => (ha.trans_le hx.1).ne'
  have hclog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
  have hfc : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hdfi : IntervalIntegrable (deriv f) volume a b := hdf.intervalIntegrable_of_Icc hab
  have hlogi : IntervalIntegrable (fun x : ℝ => x⁻¹) volume a b :=
    (continuousOn_id.inv₀ hxn).intervalIntegrable_of_Icc hab
  have hfi : IntervalIntegrable (fun x => f x / x) volume a b :=
    (hfc.div continuousOn_id hxn).intervalIntegrable_of_Icc hab
  have hdmain : IntervalIntegrable (fun x => deriv f x * Real.log x) volume a b :=
    (hdf.mul hclog).intervalIntegrable_of_Icc hab
  have hsum : IntervalIntegrable
      (fun t => deriv f t * partialCoefficientSum halaszPrimeWeight t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact integrableOn_mul_sum_Icc halaszPrimeWeight ha.le hdf.integrableOn_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul halaszPrimeWeight ha.le hab hf
    hdf.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab, ← halasz_prime_weight_band f] at hAbel
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x hx => (hf x (by simpa [Set.uIcc_of_le hab] using hx)).hasDerivAt)
    (fun x hx => Real.hasDerivAt_log (hxn x (by simpa [Set.uIcc_of_le hab] using hx)))
    hdfi hlogi
  have hsplit : (∫ t in a..b, deriv f t * Real.log t + f t * t⁻¹) =
      (∫ t in a..b, deriv f t * Real.log t) + ∫ t in a..b, f t / t := by
    simp only [← div_eq_mul_inv]
    exact intervalIntegral.integral_add hdmain hfi
  rw [hsplit] at hparts
  have herr : (∫ t in a..b, deriv f t *
      (partialCoefficientSum halaszPrimeWeight t - Real.log t)) =
      (∫ t in a..b, deriv f t * partialCoefficientSum halaszPrimeWeight t) -
      ∫ t in a..b, deriv f t * Real.log t := by
    simp only [mul_sub]
    exact intervalIntegral.integral_sub hsum hdmain
  rw [herr, hAbel]
  dsimp [partialCoefficientSum] at *
  linarith

end TwoPointCorrelations

end OAI
