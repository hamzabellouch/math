import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowerLogBound
import OAI.NumberTheory.TwoPoint.Halasz.HalaszUnitEuler

namespace OAI

/-! An ordinary absolute mean bound for the constant-one correction.
A positive logarithmic convolution and the finite Euler bound retain the
full prime-discrepancy exponent. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_real_hyperbola (G : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, G p.1 p.2) =
      ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), G d m := by
  have hh := (halasz_sum_divisorsAntidiagonal (fun d m => (G d m : ℂ)) N).trans
    (halasz_hyperbola_rows (fun d m => (G d m : ℂ)) N)
  exact_mod_cast hh

lemma halasz_unit_logarithmic_sum (F : ℕ → ℂ) (hF : OneBounded F) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ * Real.log n) ≤
      halaszPrimePowerLogConstant * N *
        ∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ) := by
  have hC : 0 ≤ halaszPrimePowerLogConstant := by
    unfold halaszPrimePowerLogConstant
    positivity
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors,
        halaszPrimePowerLog d * ‖halaszUnitCorrection F (n / d)‖ :=
      sum_le_sum (fun n _ => halasz_unit_correction_log_bound F hF n)
    _ = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d),
        halaszPrimePowerLog m * ‖halaszUnitCorrection F d‖ := by
      calc
        _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
            halaszPrimePowerLog p.2 * ‖halaszUnitCorrection F p.1‖ := by
          apply sum_congr rfl
          intro n _
          exact (Nat.sum_divisorsAntidiagonal' (fun d m =>
            halaszPrimePowerLog m * ‖halaszUnitCorrection F d‖)).symm
        _ = _ := halasz_real_hyperbola (fun d m => halaszPrimePowerLog m * ‖halaszUnitCorrection F d‖) N
    _ ≤ ∑ d ∈ Icc 1 N, (halaszPrimePowerLogConstant * N) *
        (‖halaszUnitCorrection F d‖ / (d : ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hd0 : 0 < d := (mem_Icc.mp hd).1
      have hq : 1 ≤ N / d := (Nat.le_div_iff_mul_le hd0).mpr (by simpa using (mem_Icc.mp hd).2)
      rw [← sum_mul]
      calc
        _ ≤ (halaszPrimePowerLogConstant * (N / d : ℕ)) * ‖halaszUnitCorrection F d‖ :=
          mul_le_mul_of_nonneg_right (halasz_prime_power_log_sum (N / d) hq) (norm_nonneg _)
        _ ≤ (halaszPrimePowerLogConstant * ((N : ℝ) / d)) * ‖halaszUnitCorrection F d‖ := by
          gcongr
          exact Nat.cast_div_le
        _ = _ := by ring
    _ = _ := (mul_sum _ _ _).symm

lemma halasz_positive_log_to_mean (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.log N * (∑ n ∈ Icc 1 N, g n) ≤
      (∑ n ∈ Icc 1 N, g n * Real.log n) +
        (N : ℝ) * ∑ n ∈ Icc 1 N, g n / n := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hh := Real.log_le_sub_one_of_pos (div_pos hN0 hn0)
  rw [Real.log_div hN0.ne' hn0.ne'] at hh
  have hm := mul_le_mul_of_nonneg_left hh (hg n)
  have he : (N : ℝ) * (g n / n) = g n * ((N : ℝ) / n) := by ring
  rw [he]
  nlinarith [hg n]

theorem halasz_unit_correction_mean (F : ℕ → ℂ) (hF : OneBounded F)
    (hF1 : F 1 = 1) (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖) ≤
      (halaszPrimePowerLogConstant + 1) * N / Real.log N *
        Real.exp (halaszPrimeDiscrepancy F 0 N + 8) := by
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 ≤ halaszPrimePowerLogConstant + 1 := by
    unfold halaszPrimePowerLogConstant
    positivity
  have hh := halasz_positive_log_to_mean (fun n => ‖halaszUnitCorrection F n‖)
    (fun _ => norm_nonneg _) N (by omega)
  have hw := halasz_unit_logarithmic_sum F hF N
  have he := halasz_unit_correction_reciprocal F hF hF1 N
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hl).mpr
  have hmul := mul_le_mul_of_nonneg_left he
    (show 0 ≤ (halaszPrimePowerLogConstant + 1) * (N : ℝ) by positivity)
  calc
    _ ≤ (halaszPrimePowerLogConstant + 1) * N *
        ∑ n ∈ Icc 1 N, ‖halaszUnitCorrection F n‖ / (n : ℝ) := by nlinarith
    _ ≤ (halaszPrimePowerLogConstant + 1) * N *
        Real.exp (halaszPrimeDiscrepancy F 0 N + 8) := hmul
    _ = _ := by ring

/-- Near the minimizing twist the absolute unit correction has a genuine
logarithmic saving, uniformly over all allowed missing-band masks. -/
theorem halasz_near_correction_mean :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → OneBounded F →
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ t : ℝ, squaredDistance F (mrtArchimedeanTwist t) N ≤
        Real.log (Real.log N) / 8 →
      (∑ n ∈ Icc 1 N,
        ‖halaszUnitCorrection (halaszTwistedFunction (mrtMissingCoefficient F Q) t) n‖) ≤
          ((halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
            (Real.log N) ^ (-1 / (8 : ℝ)) := by
  filter_upwards [halasz_near_masked_discrepancy, Filter.eventually_ge_atTop 2]
    with N hN hN2
  intro F hF1 hF Q hQ hcut t hD
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 ≤ halaszPrimePowerLogConstant + 1 := by
    unfold halaszPrimePowerLogConstant
    positivity
  have hmean := halasz_unit_correction_mean (halaszTwistedFunction (mrtMissingCoefficient F Q) t)
    (halasz_twisted_oneBounded _ (mrtMissingCoefficient_oneBounded F hF Q) t)
    (halasz_twisted_one _ (mrtMissingCoefficient_one F hF1 Q hQ) t) N hN2
  rw [halasz_twisted_prime_discrepancy] at hmean
  apply hmean.trans
  have hdis := hN F hF Q hQ hcut t hD
  have he : Real.exp (7 / 8 * Real.log (Real.log N) + 8) =
      Real.exp 8 * (Real.log N) ^ (7 / (8 : ℝ)) := by
    rw [Real.rpow_def_of_pos hl, ← Real.exp_add]
    congr 1
    ring
  have hp : (Real.log N) ^ (7 / (8 : ℝ)) / Real.log N =
      (Real.log N) ^ (-1 / (8 : ℝ)) := by
    calc
      _ = (Real.log N) ^ (7 / (8 : ℝ)) / (Real.log N) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (Real.log N) ^ (7 / (8 : ℝ) - 1) := (Real.rpow_sub hl _ _).symm
      _ = _ := by norm_num
  calc
    _ ≤ (halaszPrimePowerLogConstant + 1) * N / Real.log N *
        Real.exp (7 / 8 * Real.log (Real.log N) + 8) := by gcongr
    _ = ((halaszPrimePowerLogConstant + 1) * Real.exp 8) * N *
        ((Real.log N) ^ (7 / (8 : ℝ)) / Real.log N) := by rw [he]; ring
    _ = _ := by rw [hp]

end TwoPointCorrelations

end OAI
