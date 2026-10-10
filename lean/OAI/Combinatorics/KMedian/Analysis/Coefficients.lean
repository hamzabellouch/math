import Mathlib
import OAI.Combinatorics.KMedian.Model

namespace OAI

section
section
namespace MetricKMedian
def MainObligation : Prop := ∀ epsilon : ℝ, 0 < epsilon →
    ∃ algorithm : Instance → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime encodeInstance id algorithm) ∧
      ∀ I, Correct epsilon I (algorithm I)

end MetricKMedian

namespace MetricKMedian.Analytic

noncomputable def A (x : ℝ) : ℝ :=
  1 + 2 * ∫ t : ℝ in 0..1, (1 - Real.exp (-t * x))

noncomputable def P (x : ℝ) : ℝ :=
  ∫ t : ℝ in 0..1, t * Real.exp (-t * x)

noncomputable def B (x : ℝ) : ℝ := 2 * P x

noncomputable def m (x : ℝ) : ℝ := A x - 1 - 2 * x * P x

theorem exp_integrable (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

theorem texp_integrable (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t * Real.exp (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

private theorem exp_derivative_integral (x : ℝ) :
    -x * (∫ t : ℝ in 0..1, Real.exp (-t * x)) = Real.exp (-x) - 1 := by
  rw [← intervalIntegral.integral_const_mul]
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.exp (-t * x))
      (-x * Real.exp (-t * x)) t := by
    intro t
    simpa only [Pi.neg_apply, id_eq, neg_mul, one_mul, mul_one, mul_neg, mul_comm]
      using (((hasDerivAt_id t).neg.mul_const x).exp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)]
  · simp
  · exact (exp_integrable x).const_mul _

private theorem texp_derivative_integral (x : ℝ) :
    (∫ t : ℝ in 0..1, Real.exp (-t * x)) - x * P x = Real.exp (-x) := by
  rw [P, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (exp_integrable x) ((texp_integrable x).const_mul x)]
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t * Real.exp (-t * x))
      (Real.exp (-t * x) - x * (t * Real.exp (-t * x))) t := by
    intro t
    have he : HasDerivAt (fun t : ℝ => Real.exp (-t * x))
        (-x * Real.exp (-t * x)) t := by
      simpa only [Pi.neg_apply, id_eq, neg_mul, one_mul, mul_one, mul_neg, mul_comm]
        using (((hasDerivAt_id t).neg.mul_const x).exp)
    convert (hasDerivAt_id t).mul he using 1 <;> try rfl
    simp only [id_eq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)]
  · simp
  · exact (exp_integrable x).sub ((texp_integrable x).const_mul x)

theorem A_eq (x : ℝ) :
    A x = 1 + 2 * (1 - ∫ t : ℝ in 0..1, Real.exp (-t * x)) := by
  rw [A, intervalIntegral.integral_sub (intervalIntegrable_const) (exp_integrable x)]
  simp

theorem coefficient_identity (x : ℝ) :
    (1 + x) * (A x - 1) = 2 * x * (1 - P x) := by
  rw [A_eq]
  have h₁ := exp_derivative_integral x
  have h₂ := texp_derivative_integral x
  nlinarith

theorem drift_identity (x : ℝ) :
    (1 + x) * A x + x * B x - 1 = 3 * x := by
  have h := coefficient_identity x
  unfold B
  nlinarith

@[simp] theorem A_zero : A 0 = 1 := by simp [A]

@[simp] theorem P_zero : P 0 = 1 / 2 := by
  simp only [P, mul_zero, Real.exp_zero, mul_one]
  norm_num

theorem A_one : A 1 = 1 + 2 / Real.exp 1 := by
  rw [A_eq]
  have h := exp_derivative_integral 1
  simp only [mul_one, neg_mul, one_mul] at h
  simp only [mul_one]
  rw [Real.exp_neg] at h
  rw [div_eq_mul_inv]
  linarith

theorem P_nonneg (x : ℝ) : 0 ≤ P x := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact mul_nonneg ht.1 (Real.exp_pos _).le

theorem P_antitone : Antitone P := by
  intro x y hxy
  apply intervalIntegral.integral_mono_on (by norm_num) (texp_integrable y) (texp_integrable x)
  intro t ht
  apply mul_le_mul_of_nonneg_left _ ht.1
  apply Real.exp_le_exp.mpr
  nlinarith [ht.1]

theorem P_le_half {x : ℝ} (hx : 0 ≤ x) : P x ≤ 1 / 2 := by
  simpa using P_antitone hx

theorem exp_neg_half_le_P {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) / 2 ≤ P x := by
  have hint : IntervalIntegrable (fun t : ℝ => t * Real.exp (-x))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := 1) (by norm_num) hint (texp_integrable x) (fun t ht =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [ht.2])) ht.1)
  rw [intervalIntegral.integral_mul_const] at h
  norm_num at h
  unfold P
  simp only [neg_mul]
  linarith

theorem P_pos {x : ℝ} (hx : 0 ≤ x) : 0 < P x := by
  exact lt_of_lt_of_le (div_pos (Real.exp_pos _) (by norm_num)) (exp_neg_half_le_P hx)

theorem one_le_A {x : ℝ} (hx : 0 ≤ x) : 1 ≤ A x := by
  have h : 0 ≤ ∫ t : ℝ in 0..1, (1 - Real.exp (-t * x)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    have hneg : -t * x ≤ 0 := by nlinarith [ht.1]
    have := Real.exp_le_one_iff.mpr hneg
    linarith
  unfold A
  linarith

theorem A_le_one_add (x : ℝ) : A x ≤ 1 + x := by
  have hi : IntervalIntegrable (fun t : ℝ => 1 - Real.exp (-t * x))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi' : IntervalIntegrable (fun t : ℝ => t * x) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := 1) (by norm_num) hi hi' (fun t _ => by
      have he := Real.add_one_le_exp (-t * x)
      nlinarith)
  rw [intervalIntegral.integral_mul_const] at h
  norm_num at h
  unfold A
  simp only [neg_mul]
  linarith

theorem A_le_two {x : ℝ} (hx : x ≤ 1) : A x ≤ 2 := by
  linarith [A_le_one_add x]

theorem m_nonneg (x : ℝ) : 0 ≤ m x := by
  have h : 0 ≤ ∫ t : ℝ in 0..1,
      (1 - Real.exp (-t * x) - x * (t * Real.exp (-t * x))) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t _
    have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (t * x))
      (Real.exp_pos (-t * x)).le
    have hexp : Real.exp (t * x) * Real.exp (-t * x) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 2
      ring
    rw [hexp] at he
    nlinarith
  have hi : IntervalIntegrable (fun t : ℝ => 1 - Real.exp (-t * x))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_sub hi ((texp_integrable x).const_mul x),
    intervalIntegral.integral_const_mul] at h
  unfold m A P
  linarith

end MetricKMedian.Analytic


end
end

end OAI
