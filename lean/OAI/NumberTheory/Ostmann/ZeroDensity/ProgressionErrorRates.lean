import OAI.NumberTheory.Ostmann.ZeroDensity.UniformPrimeProgressions
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates

namespace OAI

/-! # The two arithmetic progression precision scales

The published square-root-log theta error is sufficient on both rows of
Section 8. The discarded Page zeros have the stronger exponent `a₀ - μ`.
-/

namespace Ostmann

open Filter

theorem constant_mul_double_exp_le (K c b d : ℝ) (hK : 0 ≤ K)
    (hc : 0 < c) (hb : 0 < b) (hdb : d < b) :
    ∀ᶠ L : ℝ in atTop, K * Real.exp (-c * Real.exp (b * L)) ≤
      Real.exp (-Real.exp (d * L)) := by
  filter_upwards [arithmetic_error_absorption 0 b d K c 0 hb hb hdb hc,
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  apply le_trans _ hL
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have hKe : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  apply hKe.trans
  apply Real.exp_le_exp.mpr
  simp only [pow_zero, mul_one, zero_mul, Real.exp_zero]
  nlinarith

theorem sqrt_ge_log_scale {a L s : ℝ} (hs : Real.exp (a * L) ≤ s) :
    Real.exp ((a / 2) * L) ≤ Real.sqrt s := by
  have h := Real.sqrt_le_sqrt hs
  rw [← Real.exp_half] at h
  exact (congrArg Real.exp (by ring : (a / 2) * L = a * L / 2)).trans_le h

theorem page_gap_ge_log_scale (κ a μ L H s : ℝ) (hκ : 0 ≤ κ)
    (hH0 : 0 < H) (hH : H ≤ 2 * Real.exp (μ * L)) (hs : Real.exp (a * L) ≤ s) :
    (κ / 2) * Real.exp ((a - μ) * L) ≤ κ * s / H := by
  apply (le_div_iff₀ hH0).mpr
  calc
    _ ≤ ((κ / 2) * Real.exp ((a - μ) * L)) * (2 * Real.exp (μ * L)) :=
      mul_le_mul_of_nonneg_left hH (by positivity)
    _ = κ * Real.exp (a * L) := by
      have he : Real.exp ((a - μ) * L) * Real.exp (μ * L) = Real.exp (a * L) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = κ * (Real.exp ((a - μ) * L) * Real.exp (μ * L)) := by ring
        _ = _ := by rw [he]
    _ ≤ κ * s := mul_le_mul_of_nonneg_left hs hκ

/-- Uniform in the modulus, residue and endpoints. The factor two is an
absolute constant, and no upper endpoint scale is required. -/
theorem PublishedProgressionInput.log_interval_rate (P : PublishedProgressionInput)
    (a₀ μ δ : ℝ) (ha : 0 < a₀) (hδa : δ < a₀ / 2) (hδμ : δ < a₀ - μ)
    (haμ : 0 < a₀ - μ) :
    ∀ᶠ L : ℝ in atTop, ∀ (q Q a : ℕ), 2 ≤ Q → 1 ≤ q → q ≤ Q → a.Coprime q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp (μ * L) →
      ∀ s t : ℝ, 1 ≤ s → Real.exp (a₀ * L) ≤ s → s ≤ t → t ≤ s + 1 →
      |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
        ∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q)
          (pageCoefficient (pageAtModulus q (selectedPageZero P Q)) a)
          (pageBeta (pageAtModulus q (selectedPageZero P Q))) y| ≤
        2 * Real.exp (-Real.exp (δ * L)) := by
  filter_upwards [constant_mul_double_exp_le (18 * P.errorConstant) P.decay (a₀ / 2) δ
      (mul_nonneg (by norm_num) P.errorConstant_nonneg) P.decay_pos (by positivity) hδa,
    constant_mul_double_exp_le 1 (P.kappa / 2) (a₀ - μ) δ (by norm_num)
      (div_pos P.kappa_pos (by norm_num)) haμ hδμ] with L htheta hpage
  intro q Q a hQ hq hqQ ha hH s t hs hscale hst hshort
  have hlog : 0 < Real.log (4 * (Q : ℝ)) := by
    apply Real.log_pos
    have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have ht' : 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt s) ≤
      Real.exp (-Real.exp (δ * L)) := by
    apply le_trans _ htheta
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) P.errorConstant_nonneg)
    apply Real.exp_le_exp.mpr
    nlinarith [sqrt_ge_log_scale hscale, P.decay_pos]
  have hp' : Real.exp (-P.kappa * s / Real.log (4 * (Q : ℝ))) ≤
      Real.exp (-Real.exp (δ * L)) := by
    apply le_trans _ (by simpa only [one_mul] using hpage)
    apply Real.exp_le_exp.mpr
    have hg := page_gap_ge_log_scale P.kappa a₀ μ L (Real.log (4 * (Q : ℝ))) s
      P.kappa_pos.le hlog hH hscale
    simpa only [neg_mul, neg_div] using neg_le_neg hg
  exact (P.uniform_log_interval hQ hq hqQ ha hs hst hshort).trans (by linarith)

end Ostmann

end OAI
