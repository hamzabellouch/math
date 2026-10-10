import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianAngle
import OAI.Probability.SKBarriers.Parisi.CDFHeatPrefix
import OAI.Probability.SKBarriers.Gaussian.C1Taylor

namespace OAI

section

noncomputable section
open scoped ENNReal NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussian_covariance_derivative {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C) :
    (∫ z, z*f z ∂gaussianReal 0 1)=∫ z, df z ∂gaussianReal 0 1 := by
  have hf := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  apply gaussian_integral_mul_eq_integral_deriv f df hd
    (gaussian_integrable_bounded hf hb) (gaussian_integrable_bounded hc hdf)
  apply ((gaussian_abs_pow_integrable 1).const_mul B).mono'
    ((continuous_id.mul hf).aestronglyMeasurable)
  exact ae_of_all _ (fun z => by
    simp only [Pi.mul_apply,id_eq,Real.norm_eq_abs,abs_mul]
    simpa only [pow_one,mul_comm] using mul_le_mul_of_nonneg_left (hb z) (abs_nonneg z))

theorem gaussian_cramer_variance {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C) :
    (∫ z, df z ∂gaussianReal 0 1)^2 ≤
      (∫ z, f z^2 ∂gaussianReal 0 1)-(∫ z, f z ∂gaussianReal 0 1)^2 := by
  let m := ∫ z, f z ∂gaussianReal 0 1
  let d := ∫ z, df z ∂gaussianReal 0 1
  have hf := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hi := gaussian_integrable_bounded hf hb
  have h2 := gaussian_integrable_sq_bounded hf hB hb
  have hz : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := (memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable le_rfl
  have hz2 : Integrable (fun z : ℝ => z^2) (gaussianReal 0 1) := by
    simpa only [sq_abs] using gaussian_abs_pow_integrable 2
  have hfz : Integrable (fun z : ℝ => z*f z) (gaussianReal 0 1) := by
    apply ((gaussian_abs_pow_integrable 1).const_mul B).mono'
      ((continuous_id.mul hf).aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      simp only [Pi.mul_apply,id_eq,Real.norm_eq_abs,abs_mul]
      simpa only [pow_one,mul_comm] using mul_le_mul_of_nonneg_left (hb z) (abs_nonneg z))
  have heq (z : ℝ) : (f z-m-d*z)^2 =
      f z^2-2*m*f z+m^2-2*d*(z*f z)+2*m*d*z+d^2*z^2 := by ring
  have H : 0 ≤ ∫ z, (f z-m-d*z)^2 ∂gaussianReal 0 1 := integral_nonneg (fun _ => sq_nonneg _)
  simp_rw [heq] at H
  have hA := integral_sub h2 (hi.const_mul (2*m))
  have hB' := integral_add (h2.sub (hi.const_mul (2*m))) (integrable_const (m^2))
  have hC' := integral_sub ((h2.sub (hi.const_mul (2*m))).add (integrable_const (m^2)))
    (hfz.const_mul (2*d))
  have hD' := integral_add (((h2.sub (hi.const_mul (2*m))).add (integrable_const (m^2))).sub
    (hfz.const_mul (2*d))) (hz.const_mul (2*m*d))
  have hE' := integral_add ((((h2.sub (hi.const_mul (2*m))).add (integrable_const (m^2))).sub
    (hfz.const_mul (2*d))).add (hz.const_mul (2*m*d))) (hz2.const_mul (d^2))
  simp only [Pi.add_apply,Pi.sub_apply] at hA hB' hC' hD' hE'
  rw [hE',hD',hC',hB',hA] at H
  rw [integral_const_mul (2*m*d) (fun z : ℝ => z),
    show (∫ z : ℝ, z ∂gaussianReal 0 1)=0 from integral_id_gaussianReal] at H
  simp only [integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul,
    gaussian_second_moment,mul_zero,add_zero,mul_one,
    gaussian_covariance_derivative hd hc hb hdf] at H
  dsimp [m,d] at H ⊢
  nlinarith

theorem gaussianHeat_variance_lower {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C)
    (a x : ℝ) : a^2*(gaussianHeat a df x)^2 ≤
      gaussianHeat a (fun y => f y^2) x-(gaussianHeat a f x)^2 := by
  have HD (z : ℝ) : HasDerivAt (fun z => f (x+a*z)) (a*df (x+a*z)) z := by
    convert (hd (x+a*z)).comp z (((hasDerivAt_id z).const_mul a).const_add x) using 1 <;>
      first | rfl | ring
  have H := gaussian_cramer_variance HD (by fun_prop) hB (fun z => hb (x+a*z))
    (C:=|a| * C) (fun z => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hdf (x+a*z)) (abs_nonneg a))
  rw [integral_const_mul] at H
  simpa only [mul_pow,gaussianHeat] using H

end SK.Analytic

end
end

end OAI
