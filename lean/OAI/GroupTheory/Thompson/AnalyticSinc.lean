import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# The correlation function for the Hilbert-space oscillator

The value at zero is filled in by the derivative of sine. Uniform separation
on a positive half-line is proved using one compact interval and the elementary
bound on sine, without a limit argument at infinity.
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open Set

def sinc (q : ℝ) : ℝ := if q = 0 then 1 else Real.sin q / q

@[simp] theorem sinc_zero : sinc 0 = 1 := by simp [sinc]

theorem sinc_of_ne_zero {q : ℝ} (hq : q ≠ 0) : sinc q = Real.sin q / q := by
  simp [sinc, hq]

@[simp] theorem sinc_neg (q : ℝ) : sinc (-q) = sinc q := by
  by_cases hq : q = 0
  · simp [hq]
  · simp [sinc, hq, Real.sin_neg]

private theorem sinc_eq_update :
    sinc = Function.update (fun q : ℝ => Real.sin q / q) 0 1 := by
  funext q
  by_cases hq : q = 0 <;> simp [sinc, hq]

theorem continuous_sinc : Continuous sinc := by
  rw [continuous_iff_continuousAt]
  intro q
  rw [sinc_eq_update]
  by_cases hq : q = 0
  · subst q
    simpa only [Real.sin_zero, Real.cos_zero, sub_zero] using
      (Real.hasDerivAt_sin 0).continuousAt_div
  · exact (continuousAt_update_of_ne hq).2
      (Real.continuous_sin.continuousAt.div continuousAt_id hq)

theorem abs_sinc_lt_one {q : ℝ} (hq : q ≠ 0) : |sinc q| < 1 := by
  rw [sinc_of_ne_zero hq, abs_div]
  exact (div_lt_one (abs_pos.mpr hq)).2 (Real.abs_sin_lt_abs hq)

theorem abs_sinc_le_one (q : ℝ) : |sinc q| ≤ 1 := by
  by_cases hq : q = 0
  · simp [hq]
  · exact (abs_sinc_lt_one hq).le

theorem sinc_le_one (q : ℝ) : sinc q ≤ 1 :=
  (le_abs_self _).trans (abs_sinc_le_one q)

theorem abs_sinc_le_half_of_two_le {q : ℝ} (hq : 2 ≤ q) : |sinc q| ≤ 1 / 2 := by
  have hqpos : 0 < q := by linarith
  rw [sinc_of_ne_zero (ne_of_gt hqpos), abs_div, abs_of_pos hqpos]
  apply (div_le_iff₀ hqpos).2
  nlinarith [Real.abs_sin_le_one q]

theorem exists_uniform_sinc_gap (d : ℝ) (hd : 0 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧
      ∀ q : ℝ, d ≤ q → ε ≤ 1 - sinc q := by
  have hdmin : 0 < min d 1 := lt_min hd (by norm_num)
  have hpositive : ∀ q ∈ Icc (min d 1) 2, 0 < 1 - sinc q := by
    intro q hq
    have hqpos : 0 < q := hdmin.trans_le hq.1
    have hs : sinc q < 1 :=
      (le_abs_self _).trans_lt (abs_sinc_lt_one (ne_of_gt hqpos))
    linarith
  obtain ⟨m, hm, hbound⟩ :=
    (isCompact_Icc : IsCompact (Icc (min d 1) (2 : ℝ))).exists_forall_le'
      (continuous_const.sub continuous_sinc).continuousOn hpositive
  refine ⟨min m (1 / 2), lt_min hm (by norm_num), min_le_right _ _, ?_⟩
  intro q hq
  by_cases hq2 : q ≤ 2
  · exact (min_le_left _ _).trans
      (hbound q ⟨(min_le_left d 1).trans hq, hq2⟩)
  · have hs : sinc q ≤ 1 / 2 :=
      (le_abs_self _).trans (abs_sinc_le_half_of_two_le (le_of_not_ge hq2))
    have hhalf : (1 / 2 : ℝ) ≤ 1 - sinc q := by linarith
    exact (min_le_right _ _).trans hhalf

end ThompsonNonamenability.Analytic

end

end OAI
