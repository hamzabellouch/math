import OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseIntegral
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! Calculus for the logarithmic phases in the sparse Dirichlet Gram
kernel. The linear frequency is kept real for the later Poisson sum. -/

namespace TwoPointCorrelations

open MeasureTheory

noncomputable def halaszLogPhase (u v x : ℝ) : ℂ :=
  Complex.exp (((u*Real.log x-v*x : ℝ):ℂ)*Complex.I)

noncomputable def halaszLogSlope (u v x : ℝ) : ℝ := u/x-v

noncomputable def halaszLogReciprocalDeriv (u v x : ℝ) : ℝ :=
  u/(x^2*(halaszLogSlope u v x)^2)

lemma halasz_log_phase_norm (u v x : ℝ) : ‖halaszLogPhase u v x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma halasz_log_phase_deriv (u v x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (halaszLogPhase u v)
      (Complex.I*(halaszLogSlope u v x:ℂ)*halaszLogPhase u v x) x := by
  have hf := ((Real.hasDerivAt_log hx).const_mul u).sub ((hasDerivAt_id x).const_mul v)
  have hh := (hf.ofReal_comp.mul_const Complex.I).cexp
  convert hh using 1
  · rfl
  · dsimp only [halaszLogPhase, halaszLogSlope, Pi.sub_apply, id_eq]
    simp only [mul_one]
    push_cast
    ring

lemma halasz_log_reciprocal_deriv (u v x : ℝ) (hx : x ≠ 0)
    (hd : halaszLogSlope u v x ≠ 0) :
    HasDerivAt (fun y => (halaszLogSlope u v y)⁻¹)
      (halaszLogReciprocalDeriv u v x) x := by
  have hh := (((hasDerivAt_const x u).div (hasDerivAt_id x) hx).sub_const v).inv hd
  convert hh using 1
  · rfl
  · change u / (x^2*(u/x-v)^2) = -((0*x-u*1)/x^2)/(u/x-v)^2
    simp only [halaszLogSlope] at hd
    field_simp [hx, hd]
    ring

lemma halasz_log_phase_primitive_deriv (u v x : ℝ) (hx : x ≠ 0)
    (hd : halaszLogSlope u v x ≠ 0) :
    HasDerivAt (fun y => -Complex.I * halaszLogPhase u v y *
      ((halaszLogSlope u v y)⁻¹:ℝ))
      (halaszLogPhase u v x - Complex.I * halaszLogPhase u v x *
        (halaszLogReciprocalDeriv u v x:ℂ)) x := by
  have hh := ((halasz_log_phase_deriv u v x hx).const_mul (-Complex.I)).mul
    (halasz_log_reciprocal_deriv u v x hx hd).ofReal_comp
  convert hh using 1
  push_cast
  have hd' : (halaszLogSlope u v x:ℂ) ≠ 0 := by exact_mod_cast hd
  field_simp [hd']
  linear_combination (halaszLogPhase u v x) * Complex.I_sq

lemma halasz_log_reciprocal_integral (u v a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hd : ∀ x ∈ Set.Icc a b, halaszLogSlope u v x ≠ 0) :
    (∫ x in a..b, halaszLogReciprocalDeriv u v x) =
      (halaszLogSlope u v b)⁻¹-(halaszLogSlope u v a)⁻¹ := by
  have hx (x : ℝ) (h : x ∈ Set.Icc a b) : x ≠ 0 := (ha.trans_le h.1).ne'
  have hc : ContinuousOn (halaszLogReciprocalDeriv u v) (Set.Icc a b) := by
    apply continuousOn_const.div
      ((continuousOn_id.pow 2).mul (((continuousOn_const.div continuousOn_id hx).sub
        continuousOn_const).pow 2))
    intro x h
    exact mul_ne_zero (pow_ne_zero 2 (hx x h)) (pow_ne_zero 2 (hd x h))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x h => halasz_log_reciprocal_deriv u v x
      (hx x (by simpa only [Set.uIcc_of_le hab] using h))
      (hd x (by simpa only [Set.uIcc_of_le hab] using h)))
    (hc.intervalIntegrable_of_Icc hab)

end TwoPointCorrelations

end OAI
