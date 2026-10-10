import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselContinuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

/-! The fixed cubic Bessel kernel in logarithmic coordinates. This form
will give quantitative sign estimates for the actual theta normalization. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicBessel_scaled_heat {a t : ℝ} (ha : 0<a) (ht : 0<t) :
    (a^2)^(1/6:ℝ)*a*cubicBesselHeat (a^2) (a*t)=
      t^(-4/3:ℝ)*Real.exp (-a*(t+t⁻¹)) := by
  unfold cubicBesselHeat
  rw [Real.mul_rpow ha.le ht.le,←Real.rpow_natCast_mul ha.le]
  have hp : a^(2*(1/6:ℝ))*a*a^(-4/3:ℝ)=1 := by
    calc
      _ = a^(2*(1/6:ℝ))*a^(1:ℝ)*a^(-4/3:ℝ) := by rw [Real.rpow_one]
      _ = a^(2*(1/6:ℝ)+1+(-4/3:ℝ)) := by rw [←Real.rpow_add ha,←Real.rpow_add ha]
      _ = 1 := by norm_num
  have he : -(a^2)/(a*t)= -a*t⁻¹ := by field_simp
  rw [he]
  calc
    _ = (a^(2*(1/6:ℝ))*a*a^(-4/3:ℝ))*t^(-4/3:ℝ)*
        (Real.exp (-(a*t))*Real.exp (-a*t⁻¹)) := by ring_nf
    _ = _ := by rw [hp,one_mul,←Real.exp_add]; congr 2; ring_nf

lemma cubicBesselKernel_scaled_integral {a : ℝ} (ha : 0<a) :
    cubicBesselKernel (a^2)=
      ∫ t in Ioi (0:ℝ),t^(-4/3:ℝ)*Real.exp (-a*(t+t⁻¹)) := by
  have h := integral_comp_mul_left_Ioi' (cubicBesselHeat (a^2)) 0 ha
  rw [mul_zero,smul_eq_mul] at h
  rw [cubicBesselKernel,←h,←integral_const_mul,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  simpa only [mul_assoc] using cubicBessel_scaled_heat ha ht

lemma cubicBesselKernel_log_integral {a : ℝ} (ha : 0<a) :
    cubicBesselKernel (a^2)=
      ∫ u : ℝ,Real.exp (-u/3)*Real.exp (-2*a*Real.cosh u) := by
  rw [cubicBesselKernel_scaled_integral ha,
    ←integral_comp_exp (fun t : ℝ => t^(-4/3:ℝ)*Real.exp (-a*(t+t⁻¹)))]
  apply integral_congr_ae
  filter_upwards with u
  simp only [smul_eq_mul]
  rw [←Real.exp_mul]
  have he : Real.exp u*Real.exp (u*(-4/3))=Real.exp (-u/3) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [←mul_assoc,he,Real.cosh_eq]
  rw [Real.exp_neg]
  congr 2
  ring_nf

end CubicFirstMoment

end

end OAI
