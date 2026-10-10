import OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseCells

namespace OAI

/-! Exact primitive of the Archimedean phase, including the zero endpoint. -/

namespace TwoPointCorrelations

open MeasureTheory

lemma halasz_power_phase_eq_cpow (t x : ℝ) (hx : 0 < x) :
    halaszPowerPhase t x = (x : ℂ) ^ ((-t : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hx.le]
  unfold halaszPowerPhase
  congr 1
  push_cast
  ring

lemma halasz_power_phase_cpow_primitive (t x : ℝ) (hx : 0 ≤ x) :
    (x : ℂ) ^ ((-t : ℂ) * Complex.I + 1) = (x : ℂ) * halaszPowerPhase t x := by
  by_cases hx0 : x = 0
  · subst x
    simp only [Complex.ofReal_zero, zero_mul]
    apply Complex.zero_cpow
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re] at hr
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [Complex.cpow_add _ _ (by exact_mod_cast hx0), Complex.cpow_one,
      halasz_power_phase_eq_cpow t x hxp, mul_comm]

lemma halasz_power_phase_integral (t a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ x in a..b, halaszPowerPhase t x) =
      ((b : ℂ) * halaszPowerPhase t b - (a : ℂ) * halaszPowerPhase t a) /
        (1 + (-t : ℂ) * Complex.I) := by
  have he : (∫ x in a..b, halaszPowerPhase t x) =
      ∫ x : ℝ in a..b, (x : ℂ) ^ ((-t : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    exact halasz_power_phase_eq_cpow t x
      (lt_of_le_of_lt (le_min ha hb) hx.1)
  rw [he, integral_cpow (Or.inl (by norm_num [Complex.mul_re])),
    halasz_power_phase_cpow_primitive t b hb,
    halasz_power_phase_cpow_primitive t a ha, add_comm ((-t : ℂ) * Complex.I) 1]

lemma halasz_power_phase_intervalIntegrable (t a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (halaszPowerPhase t) volume a b := by
  apply (intervalIntegral.intervalIntegrable_cpow' (r := (-t : ℂ) * Complex.I)
    (by norm_num [Complex.mul_re])).congr_uIoo
  intro x hx
  exact (halasz_power_phase_eq_cpow t x
    (lt_of_le_of_lt (le_min ha hb) hx.1)).symm

lemma halasz_power_phase_integral_norm (t a b : ℝ) :
    ‖∫ x in a..b, halaszPowerPhase t x‖ ≤ |b - a| := by
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := 1) (f := halaszPowerPhase t)
    (fun x _ => (halasz_power_phase_norm t x).le)

end TwoPointCorrelations

end OAI
