import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SumIntegralError

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset

namespace OrdinaryLogIntegral

lemma hasDerivAt_logPrimitive (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * logPhase t y)
      ((1 + Complex.I * t) * logPhase t x) x := by
  have hh := (hasDerivAt_id x).ofReal_comp.mul (hasDerivAt_logPhase t hx)
  refine hh.congr_deriv ?_
  simp only [id_eq, Complex.ofReal_one, one_mul]
  push_cast
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  field_simp

lemma hasDerivAt_logSecond (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (y : ℂ)^2 * logPhase t y)
      ((2 + Complex.I * t) * ((x : ℂ) * logPhase t x)) x := by
  have hh := ((hasDerivAt_id x).ofReal_comp.pow 2).mul (hasDerivAt_logPhase t hx)
  refine hh.congr_deriv ?_
  simp only [id_eq, Complex.ofReal_one, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, Pi.pow_apply]
  push_cast
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  field_simp

lemma intervalIntegrable_logPhase (t : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (logPhase t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  exact (hasDerivAt_logPhase t (ne_of_gt (ha.trans_le hx.1))).continuousAt.continuousWithinAt

theorem linear_log_integral (t u v a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (1 + Complex.I * t) * (2 + Complex.I * t) *
        (∫ x in a..b, ((u*x+v : ℝ) : ℂ) * logPhase t x) =
      (u : ℂ) * (1 + Complex.I * t) *
        ((b : ℂ)^2 * logPhase t b - (a : ℂ)^2 * logPhase t a) +
      (v : ℂ) * (2 + Complex.I * t) *
        ((b : ℂ) * logPhase t b - (a : ℂ) * logPhase t a) := by
  have hcont : ContinuousOn (fun x : ℝ => ((u*x+v : ℝ) : ℂ) * logPhase t x)
      (Set.uIcc a b) := by
    refine (Complex.continuous_ofReal.comp (by fun_prop)).continuousOn.mul ?_
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (hasDerivAt_logPhase t (ne_of_gt (ha.trans_le hx.1))).continuousAt.continuousWithinAt
  have hd (x : ℝ) (hx : x ∈ Set.uIcc a b) :
      HasDerivAt (fun y : ℝ => (u : ℂ) * (1 + Complex.I * t) *
          ((y : ℂ)^2 * logPhase t y) + (v : ℂ) * (2 + Complex.I * t) *
          ((y : ℂ) * logPhase t y))
        ((1 + Complex.I * t) * (2 + Complex.I * t) *
          (((u*x+v : ℝ) : ℂ) * logPhase t x)) x := by
    rw [Set.uIcc_of_le hab] at hx
    have hx0 := ne_of_gt (ha.trans_le hx.1)
    have hh := ((hasDerivAt_logSecond t hx0).const_mul ((u : ℂ)*(1+Complex.I*t))).add
      ((hasDerivAt_logPrimitive t hx0).const_mul ((v : ℂ)*(2+Complex.I*t)))
    refine hh.congr_deriv ?_
    push_cast
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hcont.intervalIntegrable.const_mul ((1+Complex.I*t)*(2+Complex.I*t)))
  rw [intervalIntegral.integral_const_mul] at hi
  linear_combination hi

noncomputable def triangleMellin (t a H : ℝ) : ℂ :=
  (∫ x in a..a+H, ((x-a : ℝ) : ℂ) * logPhase t x) +
    ∫ x in a+H..a+2*H, ((a+2*H-x : ℝ) : ℂ) * logPhase t x

theorem triangleMellin_identity (t a H : ℝ) (ha : 0 < a) (hH : 0 ≤ H) :
    (1 + Complex.I * t) * (2 + Complex.I * t) * triangleMellin t a H =
      (a : ℂ)^2 * logPhase t a - 2 * ((a+H : ℝ) : ℂ)^2 * logPhase t (a+H) +
        ((a+2*H : ℝ) : ℂ)^2 * logPhase t (a+2*H) := by
  have hlo := linear_log_integral t 1 (-a) a (a+H) ha (by linarith)
  have hhi := linear_log_integral t (-1) (a+2*H) (a+H) (a+2*H) (by linarith) (by linarith)
  simp only [one_mul, one_mul, ← sub_eq_add_neg] at hlo
  simp only [neg_one_mul, neg_add_eq_sub] at hhi
  dsimp [triangleMellin]
  push_cast at hlo hhi ⊢
  linear_combination hlo + hhi

lemma norm_mellin_denominator (t : ℝ) :
    1+t^2 ≤ ‖(1 + Complex.I * t) * (2 + Complex.I * t)‖ := by
  have h₁ : ‖(1 + Complex.I * t : ℂ)‖^2 = 1+t^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have h₂ : ‖(2 + Complex.I * t : ℂ)‖^2 = 4+t^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  rw [norm_mul]
  have hle : ‖(1 + Complex.I * t : ℂ)‖ ≤ ‖(2 + Complex.I * t : ℂ)‖ := by
    nlinarith [norm_nonneg (1+Complex.I*t : ℂ), norm_nonneg (2+Complex.I*t : ℂ)]
  nlinarith [mul_le_mul_of_nonneg_left hle (norm_nonneg (1+Complex.I*t : ℂ))]

theorem triangleMellin_bound (t a H : ℝ) (ha : 0 < a) (hH : 0 ≤ H) :
    (1+t^2) * ‖triangleMellin t a H‖ ≤
      a^2 + 2*(a+H)^2 + (a+2*H)^2 := by
  have he := triangleMellin_identity t a H ha hH
  have hnorm (x : ℝ) : ‖(x : ℂ)^2 * logPhase t x‖ = x^2 := by
    rw [norm_mul, norm_pow, norm_logPhase, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ ‖(1 + Complex.I * t) * (2 + Complex.I * t)‖ * ‖triangleMellin t a H‖ :=
      mul_le_mul_of_nonneg_right (norm_mellin_denominator t) (norm_nonneg _)
    _ = ‖(1 + Complex.I * t) * (2 + Complex.I * t) * triangleMellin t a H‖ :=
      (norm_mul _ _).symm
    _ = _ := congrArg norm he
    _ ≤ ‖(a : ℂ)^2 * logPhase t a‖ +
        ‖2 * ((a+H : ℝ) : ℂ)^2 * logPhase t (a+H)‖ +
          ‖((a+2*H : ℝ) : ℂ)^2 * logPhase t (a+2*H)‖ := by
      exact (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ = _ := by
      rw [hnorm a, hnorm (a+2*H)]
      rw [mul_assoc (2 : ℂ), norm_mul, Complex.norm_ofNat, hnorm (a+H)]

end OrdinaryLogIntegral

end

end OAI
