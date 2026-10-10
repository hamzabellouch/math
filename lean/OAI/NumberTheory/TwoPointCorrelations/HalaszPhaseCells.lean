import OAI.NumberTheory.TwoPointCorrelations.HalaszPhaseTaylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries

namespace OAI

/-! Unit cells for the elementary power-sum approximation. Centering the
cells cancels the linear phase error, leaving a summable quadratic error. -/

namespace TwoPointCorrelations

open MeasureTheory Finset

noncomputable def halaszPowerPhase (t x : ℝ) : ℂ :=
  Complex.exp (((-t * Real.log x : ℝ) : ℂ) * Complex.I)

@[simp] lemma halasz_power_phase_norm (t x : ℝ) : ‖halaszPowerPhase t x‖ = 1 := by
  simp [halaszPowerPhase, Complex.norm_exp, Complex.mul_re]

lemma halasz_power_phase_add (t x y : ℝ) (hx : 0 < x) (hxy : 0 < x + y) :
    halaszPowerPhase t (x + y) = halaszPowerPhase t x *
      Complex.exp (((-t * Real.log (1 + y / x) : ℝ) : ℂ) * Complex.I) := by
  have he : x + y = x * (1 + y / x) := by field_simp
  have hp : 0 < 1 + y / x := by rw [← mul_pos_iff_of_pos_left hx, ← he]; exact hxy
  rw [halaszPowerPhase, he, Real.log_mul hx.ne' hp.ne', mul_add,
    Complex.ofReal_add, add_mul, Complex.exp_add]
  rfl

lemma halasz_power_phase_cell_error (t x y : ℝ) (hx : 1 ≤ x)
    (ht : |t| ≤ x) (hy : |y| ≤ 1 / 2) :
    ‖halaszPowerPhase t (x + y) -
      halaszPowerPhase t x * (1 + (((-t * (y / x) : ℝ) : ℂ) * Complex.I))‖ ≤
      (t ^ 2 + |t|) / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hxy : 0 < x + y := by linarith [(abs_le.mp hy).1]
  have hratio : |y / x| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hx0]
    apply (div_le_iff₀ hx0).mpr
    linarith
  have htratio : |t * (y / x)| ≤ 1 / 2 := by
    rw [abs_mul, abs_div, abs_of_pos hx0]
    calc
      _ ≤ x * ((1 / 2) / x) := mul_le_mul ht
        (div_le_div_of_nonneg_right hy hx0.le) (by positivity) hx0.le
      _ = 1 / 2 := by field_simp
  have hh := halasz_phase_linear_error t (y / x) hratio htratio
  have he : halaszPowerPhase t (x + y) -
      halaszPowerPhase t x * (1 + (((-t * (y / x) : ℝ) : ℂ) * Complex.I)) =
      halaszPowerPhase t x *
        (Complex.exp (((-t * Real.log (1 + y / x) : ℝ) : ℂ) * Complex.I) - 1 -
          (((-t * (y / x) : ℝ) : ℂ) * Complex.I)) := by
    rw [halasz_power_phase_add t x y hx0 hxy]
    ring
  rw [he, norm_mul, halasz_power_phase_norm, one_mul]
  apply hh.trans
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg y) hy 2
    norm_num [sq_abs] at hh
    exact hh
  rw [div_pow]
  calc
    _ ≤ 4 * (t ^ 2 + |t|) * ((1 / 4) / x ^ 2) := by gcongr
    _ = _ := by ring

lemma halasz_power_phase_continuousOn (t a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (halaszPowerPhase t) (Set.uIcc a b) := by
  have hne : ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (ha.trans_le hx.1).ne'
  unfold halaszPowerPhase
  fun_prop (disch := assumption)

lemma halasz_power_phase_cell_integral (t x : ℝ) (hx : 1 ≤ x) (ht : |t| ≤ x) :
    ‖(∫ y in (-1 / 2 : ℝ)..(1 / 2 : ℝ), halaszPowerPhase t (x + y)) -
      halaszPowerPhase t x‖ ≤ (t ^ 2 + |t|) / x ^ 2 := by
  let lin : ℝ → ℂ := fun y =>
    halaszPowerPhase t x * (1 + (((-t * (y / x) : ℝ) : ℂ) * Complex.I))
  have hlin : Continuous lin := by dsimp [lin]; fun_prop
  have hf : ContinuousOn (fun y => halaszPowerPhase t (x + y))
      (Set.uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ)) := by
    have hne : ∀ y ∈ Set.uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ), x + y ≠ 0 := by
      intro y hy
      rw [Set.uIcc_of_le (by norm_num)] at hy
      have hp : 0 < x + y := by linarith [hy.1]
      exact hp.ne'
    unfold halaszPowerPhase
    fun_prop (disch := assumption)
  have hli : (∫ y in (-1 / 2 : ℝ)..(1 / 2 : ℝ), lin y) = halaszPowerPhase t x := by
    dsimp [lin]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_div, integral_id]
      norm_num
    · exact continuous_const.intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun y : ℝ =>
        (((-t * (y / x) : ℝ) : ℂ) * Complex.I))).intervalIntegrable _ _
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (f := fun y => halaszPowerPhase t (x + y) - lin y)
    (C := (t ^ 2 + |t|) / x ^ 2) (fun y hy => by
      apply halasz_power_phase_cell_error t x y hx ht
      rw [Set.uIoc_of_le (by norm_num)] at hy
      exact abs_le.mpr ⟨by linarith [hy.1], hy.2⟩)
  rw [intervalIntegral.integral_sub hf.intervalIntegrable (hlin.intervalIntegrable _ _), hli] at hh
  norm_num at hh ⊢
  exact hh

end TwoPointCorrelations

end OAI
