import OAI.NumberTheory.Ostmann.Arithmetic.ContinuousPrimeComparison
import OAI.NumberTheory.Ostmann.ZeroDensity.ProgressionErrorRates

namespace OAI

/-! # Numerical error budgets for the weighted giant comparison -/

namespace Ostmann
open Filter

/-- The explicit published-input error bound itself has the required uniform
rate, before a continuous weight or residue-cell count is inserted. -/
theorem PublishedProgressionInput.log_interval_budget_rate (P : PublishedProgressionInput)
    (a₀ μ δ : ℝ) (hδa : δ < a₀ / 2) (hδμ : δ < a₀ - μ)
    (ha : 0 < a₀) (haμ : 0 < a₀ - μ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp (μ * L) →
      ∀ u : ℝ, Real.exp (a₀ * L) ≤ u →
      18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
        Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) ≤
          2 * Real.exp (-Real.exp (δ * L)) := by
  filter_upwards [constant_mul_double_exp_le (18 * P.errorConstant) P.decay (a₀ / 2) δ
      (mul_nonneg (by norm_num) P.errorConstant_nonneg) P.decay_pos (by positivity) hδa,
    constant_mul_double_exp_le 1 (P.kappa / 2) (a₀ - μ) δ (by norm_num)
      (div_pos P.kappa_pos (by norm_num)) haμ hδμ] with L htheta hpage
  intro Q hQ hH u hu
  have hlog : 0 < Real.log (4 * (Q : ℝ)) := by
    apply Real.log_pos
    have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have ht : 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) ≤
      Real.exp (-Real.exp (δ * L)) := by
    apply le_trans _ htheta
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) P.errorConstant_nonneg)
    apply Real.exp_le_exp.mpr
    nlinarith [sqrt_ge_log_scale hu, P.decay_pos]
  have hp : Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) ≤
      Real.exp (-Real.exp (δ * L)) := by
    apply le_trans _ (by simpa only [one_mul] using hpage)
    apply Real.exp_le_exp.mpr
    have hg := page_gap_ge_log_scale P.kappa a₀ μ L (Real.log (4 * (Q : ℝ))) u
      P.kappa_pos.le hlog hH hu
    simpa only [neg_mul, neg_div] using neg_le_neg hg
  linarith

/-- The giant row of Section 8.2 absorbs all fixed-depth variation,
normalization and residue-count costs. The threshold precedes every modulus,
endpoint and weight budget. -/
theorem PublishedProgressionInput.weighted_giant_budget_rate (P : PublishedProgressionInput)
    (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u V : ℝ, Real.exp ((49 / 1000 : ℝ) * L) ≤ u →
      V ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      V * (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
        Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ)))) ≤
          Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) := by
  filter_upwards [P.log_interval_budget_rate (49 / 1000) (12 / 1000) (18 / 1000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    arithmetic_error_absorption (12 / 1000) (18 / 1000) (14 / 1000) C 1 d
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    constant_mul_double_exp_le 2 1 (14 / 1000) (13 / 1000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)] with L hE hcost htwo
  intro Q hQ hlog u V hu hV
  have hnonneg : 0 ≤ 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
      Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) P.errorConstant_nonneg)
      (Real.exp_pos _).le) (Real.exp_pos _).le
  calc
    _ ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) *
        (2 * Real.exp (-Real.exp ((18 / 1000 : ℝ) * L))) :=
      mul_le_mul hV (hE Q hQ hlog u hu) hnonneg (Real.exp_pos _).le
    _ = 2 * (Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) *
        Real.exp (-Real.exp ((18 / 1000 : ℝ) * L))) := by ring
    _ ≤ 2 * Real.exp (-Real.exp ((14 / 1000 : ℝ) * L)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [neg_mul, one_mul] using hcost
    _ ≤ _ := by simpa only [neg_mul, one_mul] using htwo

end Ostmann

end OAI
