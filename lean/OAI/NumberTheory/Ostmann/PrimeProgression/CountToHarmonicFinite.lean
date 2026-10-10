import OAI.NumberTheory.Ostmann.PrimeProgression.CountToHarmonicEndpoint
import OAI.NumberTheory.Ostmann.PrimeProgression.CountToHarmonicError
import OAI.NumberTheory.Ostmann.PrimeProgression.CountToHarmonicLog

namespace OAI

open Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

open scoped BigOperators
open Set MeasureTheory
open Ostmann.Dirichlet.PrimeCountAbel (logarithmicIntegral)
namespace Ostmann.Arithmetic.PrimeProgression

theorem harmonicProgression_error_of_count_error (M : ℕ) (r : ℤ) {lo hi δ : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hA : 2 ≤ Real.exp lo)
    (herror : ∀ x ∈ Icc (Real.exp lo) (Real.exp hi),
      |((Erdos970.Erdos970Dependency.SiegelWalfisz.intervalPrimes 0 x M r).card : ℝ) -
          logarithmicIntegral x / (M.totient : ℝ)| ≤ δ * x) :
    |harmonicProgression ⌊Real.exp hi⌋₊ M (r : ZMod M) lo hi - harmonicIntegral M lo hi| ≤
      (2 + hi - lo) * δ + Real.exp (-lo) := by
  have hAB : Real.exp lo ≤ Real.exp hi := Real.exp_le_exp.mpr hlohi
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hmain : ∀ t ∈ Icc (Real.exp lo) (Real.exp hi),
      HasDerivAt (fun x => logarithmicIntegral x / (M.totient : ℝ))
        ((M.totient : ℝ)⁻¹ / Real.log t) t := by
    intro t ht
    exact progression_main_hasDerivAt M (hA.trans ht.1)
  have hcont : ContinuousOn (fun t : ℝ => (M.totient : ℝ)⁻¹ / Real.log t)
      (Icc (Real.exp lo) (Real.exp hi)) := by
    simpa only [div_eq_mul_inv] using
      (continuousOn_log_inv (B := Real.exp hi) (by linarith : 1 < Real.exp lo)).const_mul
        (M.totient : ℝ)⁻¹
  have he : ∀ x ∈ Icc (Real.exp lo) (Real.exp hi),
      |cumulativeSum (primeCoefficient M (r : ZMod M)) x -
        logarithmicIntegral x / (M.totient : ℝ)| ≤ δ * x := by
    intro x hx
    rw [cumulativeSum_primeCoefficient M r ((Real.exp_pos lo).le.trans hx.1)]
    exact herror x hx
  have h := reciprocal_count_error_bound (primeCoefficient M (r : ZMod M))
    (fun x => logarithmicIntegral x / (M.totient : ℝ))
    (fun x => (M.totient : ℝ)⁻¹ / Real.log x) (Real.exp_pos lo) hAB hmain hcont he
  rw [reciprocal_primeCoefficient_sum, progression_main_integral_eq M hlo hhi] at h
  simp only [Real.log_exp] at h
  have hleft := closed_left_endpoint_error M (r : ZMod M) lo hi
  have hid : harmonicProgression ⌊Real.exp hi⌋₊ M (r : ZMod M) lo hi - harmonicIntegral M lo hi =
      (harmonicProgression ⌊Real.exp hi⌋₊ M (r : ZMod M) lo hi -
        ∑ n ∈ openLogPrimeSupport M (r : ZMod M) lo hi, (n : ℝ)⁻¹) +
      ((∑ n ∈ openLogPrimeSupport M (r : ZMod M) lo hi, (n : ℝ)⁻¹) - harmonicIntegral M lo hi) := by ring
  rw [hid]
  calc
    _ ≤ |harmonicProgression ⌊Real.exp hi⌋₊ M (r : ZMod M) lo hi -
          ∑ n ∈ openLogPrimeSupport M (r : ZMod M) lo hi, (n : ℝ)⁻¹| +
        |(∑ n ∈ openLogPrimeSupport M (r : ZMod M) lo hi, (n : ℝ)⁻¹) - harmonicIntegral M lo hi| :=
      abs_add_le _ _
    _ ≤ Real.exp (-lo) + (2 + hi - lo) * δ :=
      add_le_add (by simpa only [abs_of_nonneg hleft.1] using hleft.2) h
    _ = _ := by ring

theorem harmonicProgression_error_short_interval (M : ℕ) (r : ℤ) {lo hi δ : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hlen : hi - lo ≤ 1) (hA : 2 ≤ Real.exp lo)
    (hδ : 0 ≤ δ)
    (herror : ∀ x ∈ Icc (Real.exp lo) (Real.exp hi),
      |((Erdos970.Erdos970Dependency.SiegelWalfisz.intervalPrimes 0 x M r).card : ℝ) -
          logarithmicIntegral x / (M.totient : ℝ)| ≤ δ * x) :
    |harmonicProgression ⌊Real.exp hi⌋₊ M (r : ZMod M) lo hi - harmonicIntegral M lo hi| ≤
      3 * δ + Real.exp (-lo) := by
  apply (harmonicProgression_error_of_count_error M r hlo hlohi hA herror).trans
  have h := mul_le_mul_of_nonneg_right (show 2 + hi - lo ≤ 3 by linarith) hδ
  linarith

end Ostmann.Arithmetic.PrimeProgression

end OAI
