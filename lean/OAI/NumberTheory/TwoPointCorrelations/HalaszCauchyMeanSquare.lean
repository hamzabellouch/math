import OAI.NumberTheory.TwoPointCorrelations.HalaszUnitPrimeWindows
import Mathlib.Analysis.PSeries

namespace OAI

/-! Summing the translated unit-window estimates against the Cauchy
weight gives the global weighted mean square used in the Perron argument. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma halasz_polynomial_norm_le {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) (t : ℝ) :
    ‖mrtExponentialPolynomial S a freq t‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  unfold mrtExponentialPolynomial
  exact (norm_sum_le _ _).trans (by
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, le_refl])

lemma halasz_cauchy_polynomial_integrable {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (freq : ι → ℝ) :
    Integrable (fun t : ℝ => ‖mrtExponentialPolynomial S a freq t‖ ^ 2 * (1 + t ^ 2)⁻¹) := by
  have hc : Continuous (fun t : ℝ =>
      ‖mrtExponentialPolynomial S a freq t‖ ^ 2 * (1 + t ^ 2)⁻¹) := by
    apply ((halasz_polynomial_continuous S a freq).norm.pow 2).mul
    exact (continuous_const.add (continuous_id.pow 2)).inv₀
      (fun t => ne_of_gt (by positivity : (0 : ℝ) < 1 + t ^ 2))
  apply (integrable_inv_one_add_sq.const_mul ((∑ i ∈ S, ‖a i‖) ^ 2)).mono'
    hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (halasz_polynomial_norm_le S a freq t) 2)
    (by positivity)

lemma halasz_cauchy_integer_summable : Summable (fun k : ℤ => (1 + (k : ℝ) ^ 2)⁻¹) := by
  have hsingle : Summable (fun k : ℤ => if k = 0 then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp only [mem_singleton] at hk
    simp [hk]
  have hp := (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).add hsingle
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ hp
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · rw [ite_eq_right hk, add_zero]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_ne_zero hk0)
      (show (k : ℝ) ^ 2 ≤ 1 + (k : ℝ) ^ 2 by linarith)

lemma halasz_cauchy_weight_window {k t : ℝ} (ht : t ∈ Set.Icc (k - 1 / 2) (k + 1 / 2)) :
    (1 + t ^ 2)⁻¹ ≤ 2 * (1 + k ^ 2)⁻¹ := by
  have hgap : (k - t) ^ 2 ≤ 1 / 4 := by
    have hp := mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2)
    nlinarith
  have hden : 1 + k ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (2 * t - k)]
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hkpos : 0 < 1 + k ^ 2 := by positivity
  simpa only [div_eq_mul_inv, one_mul] using
    (div_le_div_iff₀ hpos hkpos).mpr (show (1 : ℝ) * (1 + k ^ 2) ≤ 2 * (1 + t ^ 2) by nlinarith)

theorem halasz_prime_mean_square_cauchy : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ a : ℕ → ℂ,
      (∫ t : ℝ, ‖mrtExponentialPolynomial P
        (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ))
        (fun p => -Real.log (p : ℝ)) t‖ ^ 2 * (1 + t ^ 2)⁻¹) ≤
        C * ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p) := by
  obtain ⟨C, hC, hm⟩ := halasz_prime_mean_square_unit
  let W := ∑' k : ℤ, (1 + (k : ℝ) ^ 2)⁻¹
  have hW : 0 ≤ W := tsum_nonneg (fun _ => by positivity)
  refine ⟨C * (1 + 2 * W), by positivity, ?_⟩
  intro P hP a
  let D := mrtExponentialPolynomial P
    (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ)) (fun p => -Real.log (p : ℝ))
  let M := ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)
  have hM : 0 ≤ M := sum_nonneg (fun p hp => mul_nonneg (sq_nonneg _)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _)))
  have hi : Integrable (fun t : ℝ => ‖D t‖ ^ 2 * (1 + t ^ 2)⁻¹) :=
    halasz_cauchy_polynomial_integrable P _ _
  have hs := hi.hasSum_intervalIntegral (-(1 / 2 : ℝ))
  have hb (k : ℤ) : (∫ t in (-(1 / 2 : ℝ) + k)..(-(1 / 2 : ℝ) + k + 1),
      ‖D t‖ ^ 2 * (1 + t ^ 2)⁻¹) ≤ (2 * C * M) * (1 + (k : ℝ) ^ 2)⁻¹ := by
    have he1 : -(1 / 2 : ℝ) + k = (k : ℝ) - 1 / 2 := by ring
    have he2 : -(1 / 2 : ℝ) + k + 1 = (k : ℝ) + 1 / 2 := by ring
    rw [he2, he1]
    have hc := (halasz_polynomial_continuous P
      (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ))
      (fun p => -Real.log (p : ℝ))).norm.pow 2
    calc
      _ ≤ ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
          (2 * (1 + (k : ℝ) ^ 2)⁻¹) * ‖D t‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on (by linarith) hi.intervalIntegrable
          ((hc.const_mul _).intervalIntegrable _ _)
        intro t ht
        simpa only [D, Pi.pow_apply, mul_comm] using mul_le_mul_of_nonneg_left
          (halasz_cauchy_weight_window ht) (sq_nonneg ‖D t‖)
      _ = (2 * (1 + (k : ℝ) ^ 2)⁻¹) *
          ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), ‖D t‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ (2 * (1 + (k : ℝ) ^ 2)⁻¹) * (C * M) :=
        mul_le_mul_of_nonneg_left (hm P hP a k) (by positivity)
      _ = _ := by ring
  have hsum := hs.summable.tsum_le_tsum hb (halasz_cauchy_integer_summable.mul_left (2 * C * M))
  rw [hs.tsum_eq, tsum_mul_left] at hsum
  change _ ≤ _
  change _ ≤ C * (1 + 2 * W) * M
  change _ ≤ 2 * C * M * W at hsum
  nlinarith

end TwoPointCorrelations

end OAI
