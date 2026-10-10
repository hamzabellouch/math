import OAI.NumberTheory.Ostmann.ZeroDensity.WeightedProgressionRates

namespace OAI

/-! # The full bulk progression error, including derivative cuts and endpoints -/

namespace Ostmann
open Filter

/-- The Section 8 bulk row absorbs variable polynomial-cut counts, residue
counts, and the complete smooth budget. No fixed bound on the number of roots
is needed: those costs are all included in `V`. -/
theorem PublishedProgressionInput.bulk_full_progression_budget_rate (P : PublishedProgressionInput)
    (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) →
      ∀ u V : ℝ, Real.exp ((39 / 10000 : ℝ) * L) ≤ u →
      V ≤ Real.exp (C * L ^ d + C * L * Real.exp ((14 / 10000 : ℝ) * L)) →
      V * (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
        Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u)) ≤
          Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) := by
  filter_upwards [P.log_interval_budget_rate (39 / 10000) (12 / 10000) (18 / 10000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    arithmetic_error_absorption (14 / 10000) (18 / 10000) (13 / 10000) C 1 d
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    constant_mul_double_exp_le 4 1 (13 / 10000) (125 / 100000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with L hP hcost hfour hL
  intro Q hQ hlog u V hu hV
  have hsmall : Real.exp (-u) ≤ Real.exp (-Real.exp ((18 / 10000 : ℝ) * L)) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact (Real.exp_le_exp.mpr (by nlinarith)).trans hu
  have he := hP Q hQ hlog u hu
  have hC := P.errorConstant_nonneg
  have hn : 0 ≤ 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
      Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u) := by positivity
  have htotal : 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
      Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) + 2 * Real.exp (-u) ≤
      4 * Real.exp (-Real.exp ((18 / 10000 : ℝ) * L)) := by linarith
  calc
    _ ≤ Real.exp (C * L ^ d + C * L * Real.exp ((14 / 10000 : ℝ) * L)) *
        (4 * Real.exp (-Real.exp ((18 / 10000 : ℝ) * L))) :=
      mul_le_mul hV htotal hn (Real.exp_pos _).le
    _ = 4 * (Real.exp (C * L ^ d + C * L * Real.exp ((14 / 10000 : ℝ) * L)) *
        Real.exp (-Real.exp ((18 / 10000 : ℝ) * L))) := by ring
    _ ≤ 4 * Real.exp (-Real.exp ((13 / 10000 : ℝ) * L)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [one_mul, neg_mul] using hcost
    _ ≤ _ := by simpa only [one_mul, neg_mul] using hfour

end Ostmann

end OAI
