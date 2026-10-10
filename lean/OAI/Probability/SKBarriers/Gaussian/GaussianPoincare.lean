import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianAngle

namespace OAI

section

noncomputable section
open scoped NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussianAngle_hasDerivAt {f df g dg : ℝ → ℝ}
    (hdf : ∀ x, HasDerivAt f (df x) x) (hfc : Continuous df)
    (hdg : ∀ x, HasDerivAt g (dg x) x) (hgc : Continuous dg)
    {B C D E : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |df x| ≤ C)
    (hd : ∀ x, |g x| ≤ D) (he : ∀ x, |dg x| ≤ E) (θ : ℝ) :
    HasDerivAt (gaussianAngle f g) (-Real.sin θ*gaussianAngle df dg θ) θ := by
  have hf := continuous_iff_continuousAt.mpr (fun x => (hdf x).continuousAt)
  have H := gaussianPair_rotation_derivative hf hdg hgc hB hD hE hb hd he θ
  rw [gaussianPair_rotation_stein hdf hfc hgc hB hC hE hb hc he θ] at H
  exact H

theorem gaussian_variance_angle_identity {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C) :
    (∫ x, f x^2 ∂gaussianReal 0 1)-(∫ x, f x ∂gaussianReal 0 1)^2=
      ∫ θ in 0..Real.pi/2, Real.sin θ*gaussianAngle df df θ := by
  have hf := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hdc := gaussianAngle_continuous hc hc hC hdf hdf
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=0) (b:=Real.pi/2)
    (fun θ _ => gaussianAngle_hasDerivAt hd hc hd hc hB hC hB hC hb hdf hb hdf θ)
    ((Real.continuous_sin.neg.mul hdc).intervalIntegrable _ _)
  simp_rw [neg_mul] at H
  rw [intervalIntegral.integral_neg, gaussianAngle_zero f hf,
    gaussianAngle_pi_half hf hf hB hb hb] at H
  nlinarith

theorem gaussian_strict_poincare_of_derivative_nonconstant {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C)
    (hne : ¬∃ c, ∀ x, df x=c) :
    (∫ x, f x^2 ∂gaussianReal 0 1)-(∫ x, f x ∂gaussianReal 0 1)^2 <
      ∫ x, df x^2 ∂gaussianReal 0 1 := by
  let A : ℝ := ∫ x, df x^2 ∂gaussianReal 0 1
  have hdc := gaussianAngle_continuous hc hc hC hdf hdf
  have hpos : 0<∫ θ in 0..Real.pi/2, Real.sin θ*(A-gaussianAngle df df θ) := by
    apply intervalIntegral.integral_pos (by positivity)
      ((Real.continuous_sin.mul (continuous_const.sub hdc)).continuousOn)
    · intro θ hθ
      exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2,Real.pi_pos]))
        (sub_nonneg.mpr (gaussianAngle_le_square hc hC hdf θ))
    · refine ⟨Real.pi/2,⟨by positivity,le_rfl⟩,?_⟩
      change 0 < Real.sin (Real.pi/2)*(A-gaussianAngle df df (Real.pi/2))
      rw [Real.sin_pi_div_two,one_mul,gaussianAngle_pi_half hc hc hC hdf hdf]
      exact sub_pos.mpr (by simpa only [A,pow_two] using gaussian_variance_pos hc hC hdf hne)
  have H := gaussian_variance_angle_identity hd hc hB hC hb hdf
  have heq : (∫ θ in 0..Real.pi/2, Real.sin θ*(A-gaussianAngle df df θ))=
      A-(∫ θ in 0..Real.pi/2, Real.sin θ*gaussianAngle df df θ) := by
    simp_rw [mul_sub]
    have HS := intervalIntegral.integral_sub (μ:=volume)
      ((Real.continuous_sin.mul (continuous_const (y:=A))).intervalIntegrable 0 (Real.pi/2))
      ((Real.continuous_sin.mul hdc).intervalIntegrable 0 (Real.pi/2))
    simp only [Pi.mul_apply] at HS
    rw [HS,intervalIntegral.integral_mul_const,
      integral_sin,Real.cos_zero,Real.cos_pi_div_two]
    ring
  rw [heq,← H] at hpos
  exact sub_pos.mp hpos

theorem bounded_derivative_constant_imp_constant {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, |f x| ≤ B) (hc : ∃ c, ∀ x, df x=c) : ∃ c, ∀ x, f x=c := by
  obtain ⟨c,hc⟩ := hc
  have hder (x : ℝ) : HasDerivAt (fun y => f y-c*y) 0 x := by
    convert (hd x).sub ((hasDerivAt_id x).const_mul c) using 1 <;> first | rfl | simp_all
  have heq (x : ℝ) : f x=c*x+f 0 := by
    have H := is_const_of_deriv_eq_zero (fun y => (hder y).differentiableAt)
      (fun y => (hder y).deriv) x 0
    linarith
  have hz : c=0 := by
    by_contra hn
    have H := (abs_le.mp (hb ((2*B+1)/c))).2
    rw [heq] at H
    have hm : c*((2*B+1)/c)=2*B+1 := by field_simp
    rw [hm] at H
    have H0 := (abs_le.mp (hb 0)).1
    linarith
  refine ⟨f 0,fun x => ?_⟩
  simpa only [hz,zero_mul,zero_add] using heq x

theorem gaussian_strict_poincare {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C)
    (hne : ¬∃ c, ∀ x, f x=c) :
    (∫ x, f x^2 ∂gaussianReal 0 1)-(∫ x, f x ∂gaussianReal 0 1)^2 <
      ∫ x, df x^2 ∂gaussianReal 0 1 := by
  apply gaussian_strict_poincare_of_derivative_nonconstant hd hc hB hC hb hdf
  intro h
  exact hne (bounded_derivative_constant_imp_constant hd hB hb h)

end SK.Analytic

end
end

end OAI
