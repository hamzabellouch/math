import OAI.Combinatorics.ExpectationThreshold.RoundingMain
import OAI.Combinatorics.ExpectationThreshold.ThresholdAttainment

namespace OAI

/-!
# Integral and fractional expectation thresholds

The fractional threshold is genuinely attained with budget one half. Rounding
that attained cover gives an integral cover at the threshold divided by
`25 * 512^4`, still with budget one half and without a support-size restriction.
-/

namespace TalagrandThreshold

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Talagrand's threshold comparison with the explicit constant `25 * 512^4`.
The coefficient 25 is an integer factor, and both feasible sets use budget
one half. The fractional cover ranges over every subset of the ground set. -/
theorem talagrand_expectation_threshold_equivalence [Nonempty α]
    (F : Family α) (_hF : F.Nonempty) (hproper : F ≠ Finset.univ)
    (hIncreasing : Increasing F) :
    qf F ≤ ((25 : ℝ) * (512 : ℝ) ^ 4) * q F := by
  have hempty : (∅ : Finset α) ∉ F := hIncreasing.empty_not_mem hproper
  have hqf0 : 0 ≤ qf F := qf_nonneg F hempty
  have hqf1 : qf F ≤ 1 := qf_le_one F hempty
  have hsmall : Small (qf F / ((25 : ℝ) * (512 : ℝ) ^ 4)) F :=
    fractionalSmall_rounding F hqf0 hqf1 (fractionalSmall_qf F hempty)
  have hscaled0 : 0 ≤ qf F / ((25 : ℝ) * (512 : ℝ) ^ 4) :=
    div_nonneg hqf0 rounding_constant_pos.le
  have hscaled1 : qf F / ((25 : ℝ) * (512 : ℝ) ^ 4) ≤ 1 :=
    (div_le_one rounding_constant_pos).mpr
      (hqf1.trans (by norm_num : (1 : ℝ) ≤ (25 : ℝ) * (512 : ℝ) ^ 4))
  have hle := le_q_of_small hscaled0 hscaled1 hsmall
  calc
    qf F ≤ q F * ((25 : ℝ) * (512 : ℝ) ^ 4) :=
      (div_le_iff₀ rounding_constant_pos).mp hle
    _ = ((25 : ℝ) * (512 : ℝ) ^ 4) * q F := mul_comm _ _

end TalagrandThreshold

end OAI
