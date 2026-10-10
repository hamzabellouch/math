import OAI.NumberTheory.CubicMoment.Estimates.RieszFubini
import OAI.NumberTheory.CubicMoment.Estimates.GaussianDuality

namespace OAI

/-! Mellin change of variables for the Gaussian Riesz identity. -/

noncomputable section
open scoped SchwartzMap
open MeasureTheory Set
namespace CubicFirstMoment

lemma gaussian_mellin_identity (F : 𝓢(ℂ,ℂ)) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (Real.Gamma a:ℂ)*(∫ z : ℂ, ((‖z‖^(-2*a):ℝ):ℂ)*F z) =
      ∫ t in Ioi (0:ℝ), (t^(a-1):ℝ)*
        (∫ z : ℂ, F z*Complex.exp (-(t:ℂ)*‖z‖^2)) := by
  rw [riesz_integral_eq_gaussian_integral F ha ha1]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  unfold rieszGaussianWeight
  rw [Complex.ofReal_mul,Complex.ofReal_exp]
  push_cast
  rw [show -((‖z‖:ℂ)^2)*(t:ℂ) = -(t:ℂ)*(‖z‖:ℂ)^2 by ring]
  ring

lemma inverse_mellin_change (H : ℝ → ℂ) (a : ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ t in Ioi (0:ℝ), (t^(a-2):ℝ)*H (c/t)) =
      (c^(a-1):ℝ)*(∫ v in Ioi (0:ℝ), (v^(-a):ℝ)*H v) := by
  have hi := integral_comp_rpow_Ioi (fun u : ℝ => (u^(-a):ℝ)*H (c*u))
    (show (-1:ℝ) ≠ 0 by norm_num)
  have hs : (∫ t in Ioi (0:ℝ), (t^(a-2):ℝ)*H (c/t)) =
      ∫ u in Ioi (0:ℝ), (u^(-a):ℝ)*H (c*u) := by
    rw [← hi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    have hp : t^(a-2) = t^((-1:ℝ)-1)*(t^(-1:ℝ))^(-a) := by
      rw [← Real.rpow_mul ht.le,← Real.rpow_add ht]
      congr 1
      ring
    rw [hp]
    simp only [abs_neg,abs_one,one_mul,Real.rpow_neg_one,Complex.real_smul]
    push_cast
    rw [div_eq_mul_inv]
    ring
  rw [hs]
  have hscale := integral_comp_mul_left_Ioi (fun v : ℝ => (v^(-a):ℝ)*H v) 0 hc
  simp only [mul_zero] at hscale
  have hpow (u : ℝ) (hu : u ∈ Ioi (0:ℝ)) :
      ((u^(-a):ℝ):ℂ)*H (c*u) = ((c^a:ℝ):ℂ)*(((c*u)^(-a):ℝ):ℂ)*H (c*u) := by
    rw [Real.mul_rpow hc.le hu.le,Complex.ofReal_mul]
    have he : c^a*c^(-a) = (1:ℝ) := by rw [← Real.rpow_add hc]; simp
    rw [← mul_assoc,← Complex.ofReal_mul (c^a) (c^(-a)),he]
    simp
  calc
    _ = ((c^a:ℝ):ℂ)*(∫ u in Ioi (0:ℝ), ((c*u)^(-a):ℝ)*H (c*u)) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi (fun u hu => by
        simpa only [mul_assoc] using hpow u hu)
    _ = _ := by
      rw [hscale,Complex.real_smul]
      have he : c^a*c⁻¹ = c^(a-1) := by
        simpa only [Real.rpow_one,div_eq_mul_inv] using (Real.rpow_sub hc a 1).symm
      rw [← mul_assoc,← Complex.ofReal_mul,he]

end CubicFirstMoment

end

end OAI
