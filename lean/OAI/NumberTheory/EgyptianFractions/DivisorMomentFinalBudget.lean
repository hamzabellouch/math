import OAI.NumberTheory.EgyptianFractions.DivisorMomentAbsorption

namespace OAI
open Filter

namespace Problem337.DivisorMomentFinalBudget

/-- The square-root cutoff in the harmonic-prefix estimate satisfies the
uniform large-class parameter window. -/
theorem eventually_sqrt_cutoff_window (D : ℝ) :
    ∀ᶠ S : ℝ in atTop, ∀ v Y : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      0 ≤ v ∧ 2 ≤ Real.sqrt Y ∧ Real.log (Real.sqrt Y) ≤ D * S := by
  have hlog := Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / 12 by norm_num)
  filter_upwards [hlog, eventually_ge_atTop (2 : ℝ)] with S hlog hS
  intro v Y hvlow hvup hYlow hYup
  have hSpos : 0 < S := by linarith
  have hlogpos : 0 < Real.log S := Real.log_pos (by linarith)
  have hlogbound : Real.log S ≤ S / 12 := by
    simpa only [Real.norm_eq_abs, id_eq, abs_of_pos hSpos,
      abs_of_pos hlogpos, one_div_mul_eq_div] using hlog
  have hv6 : 6 ≤ v := by
    apply le_trans _ hvlow
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log S)).mpr
    linarith
  have hY4 : 4 ≤ Y := by
    have := Real.add_one_le_exp (v / 2)
    linarith
  have hYpos : 0 < Y := by linarith
  have hlogY : Real.log Y ≤ v := (Real.log_le_iff_le_exp hYpos).mpr hYup
  refine ⟨by linarith, ?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    norm_num
    exact hY4
  · rw [Real.log_sqrt hYpos.le]
    linarith

/-- Final loss absorption with the large-class majorant supplied explicitly.
This helper isolates the harmless square-root cutoff and finite-band count
from the number-theoretic class estimates. -/
theorem final_budget_of_large_majorant
    (D r C A B : ℝ) (hA : 0 ≤ A)
    (hlarge : ∀ᶠ S : ℝ in atTop, ∀ v Z : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S → 2 ≤ Z →
      Real.log Z ≤ D * S →
      2 * Real.exp (r * (1 + Real.log ((D + 1) * S / v)) *
        v ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log Z)) ≤
      Real.exp (A * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) +
        B * Real.log S)) :
    ∀ᶠ S : ℝ in atTop, ∀ v Y : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      2 * Real.exp (r * (1 + Real.log ((D + 1) * S / v)) *
        v ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log (Real.sqrt Y))) +
        2 * Real.exp (-v / 100) + (6 / Real.log 2) * Real.log S ≤
      Real.exp (S ^ (1 / 4 : ℝ)) := by
  filter_upwards [hlarge, eventually_sqrt_cutoff_window D,
    DivisorMomentAbsorption.eventually_absorb_large_contribution A B
      (6 / Real.log 2) hA] with S hlarge hwindow habsorb
  intro v Y hvlow hvup hYlow hYup
  obtain ⟨hv0, hZlow, hZup⟩ := hwindow v Y hvlow hvup hYlow hYup
  have hmajor := hlarge v (Real.sqrt Y) hvlow hvup hZlow hZup
  have hfinal := habsorb (-v / 100) (by linarith)
  linarith

/-- Exact final numerical budget for the large, small, and dyadic intermediate
classes. All growth estimates are unconditional and uniform in both windows. -/
theorem eventually_divisor_moment_final_budget
    (D r C : ℝ) (hD : 1 ≤ D) (hr : 0 ≤ r) (hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop, ∀ v Y : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      2 * Real.exp (r * (1 + Real.log ((D + 1) * S / v)) *
        v ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log (Real.sqrt Y))) +
        2 * Real.exp (-v / 100) + (6 / Real.log 2) * Real.log S ≤
      Real.exp (S ^ (1 / 4 : ℝ)) := by
  exact final_budget_of_large_majorant D r C
    (DivisorMomentAbsorption.largeCoefficient D r)
    (DivisorMomentAbsorption.harmonicCoefficient D C)
    (DivisorMomentAbsorption.largeCoefficient_nonneg hD hr)
    (DivisorMomentAbsorption.eventually_large_contribution_bound D r C hD hr hC)

/-- The weighted form directly bounds the sum of the three class contributions. -/
theorem eventually_divisor_moment_weighted_budget
    (D r C : ℝ) (hD : 1 ≤ D) (hr : 0 ≤ r) (hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop, ∀ v Y : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      2 * Y * Real.exp (r * (1 + Real.log ((D + 1) * S / v)) *
        v ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log (Real.sqrt Y))) +
        2 * Y * Real.exp (-v / 100) +
        Y * ((6 / Real.log 2) * Real.log S) ≤
      Y * Real.exp (S ^ (1 / 4 : ℝ)) := by
  filter_upwards [eventually_divisor_moment_final_budget D r C hD hr hC]
    with S hS
  intro v Y hvlow hvup hYlow hYup
  have h := mul_le_mul_of_nonneg_left (hS v Y hvlow hvup hYlow hYup)
    ((Real.exp_pos (v / 2)).le.trans hYlow)
  nlinarith

end Problem337.DivisorMomentFinalBudget

end OAI
