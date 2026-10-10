import OAI.Analysis.KadisonKastler.CoreTraceWeightShift
import OAI.Analysis.KadisonKastler.CharacterContinuity

namespace OAI

/-! # Balance of the two Tomita weights under the core frequency shift -/

namespace KadisonKastler

noncomputable section

theorem coreTrace_exp_sqrt_balance {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Real.exp (Real.pi * (resolventLogFrequency s / (2 * Real.pi))) * Real.sqrt s =
      Real.sqrt (1 - s) := by
  have hπ : Real.pi * (resolventLogFrequency s / (2 * Real.pi)) =
      resolventLogFrequency s / 2 := by field_simp
  rw [hπ]
  have he : Real.exp (resolventLogFrequency s / 2) ^ 2 =
      Real.exp (resolventLogFrequency s) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hr : Real.exp (resolventLogFrequency s) * s = 1 - s := by
    rw [resolventLogFrequency, Real.exp_sub, Real.exp_log (sub_pos.mpr hs1), Real.exp_log hs]
    field_simp
  have hsq : (Real.exp (resolventLogFrequency s / 2) * Real.sqrt s) ^ 2 =
      (Real.sqrt (1 - s)) ^ 2 := by
    rw [mul_pow, he, Real.sq_sqrt hs.le, hr, Real.sq_sqrt (sub_pos.mpr hs1).le]
  exact (sq_eq_sq₀ (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg s))
    (Real.sqrt_nonneg (1 - s))).mp hsq

theorem coreTraceFrequencyFunction_spectral_balance
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (t : ℝ) :
    (Set.Ioc (0 : ℝ) 1).indicator
        (fun r => coreTraceFrequencyFunction (r + resolventLogFrequency s / (2 * Real.pi))) t *
        (Real.sqrt s : ℂ) =
      (Set.Ioc (-(resolventLogFrequency s / (2 * Real.pi)))
        (1 - resolventLogFrequency s / (2 * Real.pi))).indicator coreTraceFrequencyFunction t *
        (Real.sqrt (1 - s) : ℂ) := by
  rw [coreTraceFrequencyFunction_shift]
  have he : (Real.exp (Real.pi * (resolventLogFrequency s / (2 * Real.pi))) : ℂ) *
      (Real.sqrt s : ℂ) = (Real.sqrt (1 - s) : ℂ) := by
    exact_mod_cast coreTrace_exp_sqrt_balance hs hs1
  rw [mul_assoc, mul_comm _ (Real.sqrt s : ℂ), ← mul_assoc, he, mul_comm]

end

end KadisonKastler

end OAI
