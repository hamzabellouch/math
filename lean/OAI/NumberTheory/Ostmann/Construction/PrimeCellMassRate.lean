import OAI.NumberTheory.Ostmann.Arithmetic.BulkWeightedErrorBudget
import OAI.NumberTheory.Ostmann.Construction.OriginalHarmonicMass

namespace OAI

/-! # Uniform mass comparison for every original short cell -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem double_exp_below_original_mass (b C : ℝ) (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (-Real.exp (b * L)) ≤ Real.exp (-C * L) / 4 := by
  filter_upwards [arithmetic_exponent_absorption 0 b 0 (|C| + 4) 1 1 hb hb hb (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  have hlog : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hC := le_abs_self C
  have hL0 : 0 ≤ L := by linarith
  simp only [zero_mul, Real.exp_zero, mul_one, pow_one] at hrate
  have hx : C * L + Real.log 4 ≤ Real.exp (b * L) := by
    nlinarith [abs_nonneg C, mul_le_mul_of_nonneg_right hC hL0]
  calc
    _ ≤ Real.exp (-C * L - Real.log 4) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)]

theorem PublishedProgressionInput.short_cell_mass_error_rate (P : PublishedProgressionInput) :
    ∀ᶠ L : ℝ in atTop, ∀ (Cell : Type) [Fintype Cell] (Q : ℕ), 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      ∀ u : Cell → ℝ, (∀ c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u c) →
        (∑ c, bulkPrimeErrorFactor P Q (u c)) ≤
          Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) := by
  filter_upwards [P.bulk_full_progression_budget_rate 1 0, eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro Cell _ Q hQ hlog hcard u hu
  have hcost : (Fintype.card Cell : ℝ) ≤ Real.exp (1 * L ^ 0 +
      1 * L * Real.exp ((14 / 10000 : ℝ) * L)) := by
    apply hcard.trans
    apply Real.exp_le_exp.mpr
    simp only [pow_zero, one_mul]
    nlinarith [Real.exp_nonneg ((14 / 10000 : ℝ) * L)]
  calc
    _ ≤ ∑ _c : Cell, bulkPrimeErrorFactor P Q (Real.exp ((39 / 10000 : ℝ) * L)) :=
      Finset.sum_le_sum fun c _ => bulkPrimeErrorFactor_antitone P hQ (hu c)
    _ = (Fintype.card Cell : ℝ) * bulkPrimeErrorFactor P Q (Real.exp ((39 / 10000 : ℝ) * L)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := hrate Q hQ hlog _ _ le_rfl hcost

theorem PublishedProgressionInput.short_cell_mass_error_relative (P : PublishedProgressionInput)
    (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (Cell : Type) [Fintype Cell] (Q : ℕ), 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      ∀ u : Cell → ℝ, (∀ c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u c) →
        (∑ c, bulkPrimeErrorFactor P Q (u c)) ≤ Real.exp (-C * L) / 4 := by
  filter_upwards [P.short_cell_mass_error_rate,
    double_exp_below_original_mass (125 / 100000) C (by norm_num)] with L hrate hsmall
  intro Cell _ Q hQ hlog hcard u hu
  exact (hrate Cell Q hQ hlog hcard u hu).trans hsmall

end Ostmann

end OAI
