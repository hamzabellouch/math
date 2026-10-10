import Mathlib.MeasureTheory.Integral.Gamma

namespace OAI

/-! Laplace representations of the two radial powers in the Riesz calculation. -/

noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma laplace_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (0:ℝ), t^(a-1)*Real.exp (-b*t)) =
      Real.Gamma a*b^(-a) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := a-1) (b := b)
    (by norm_num) (by linarith) hb
  simpa only [Real.rpow_one,sub_add_cancel,div_one,one_div_one,mul_one,mul_comm] using h

lemma integrable_laplace_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t^(a-1)*Real.exp (-b*t)) (Ioi 0) := by
  by_contra h
  have hp : 0 < Real.Gamma a*b^(-a) := mul_pos (Real.Gamma_pos_of_pos ha)
    (Real.rpow_pos_of_pos hb _)
  rw [← laplace_rpow ha hb,integral_undef h] at hp
  exact lt_irrefl _ hp

/-- The singular power is a convergent integral of Gaussians away from zero. -/
lemma riesz_gaussian_representation {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z ≠ 0) :
    (∫ t in Ioi (0:ℝ), t^(a-1)*Real.exp (-t*‖z‖^2)) =
      Real.Gamma a*‖z‖^(-2*a) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h := laplace_rpow ha (sq_pos_of_pos hn)
  have he : (‖z‖^2)^(-a) = ‖z‖^(-2*a) := by
    rw [← Real.rpow_natCast ‖z‖ 2,← Real.rpow_mul hn.le]
    congr 1
    ring
  rw [he] at h
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  congr 1
  congr 1
  ring

/-- The inverted Gaussian moment is the dual radial power. -/
lemma inverse_gaussian_moment {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (0:ℝ), t^(-a-1)*Real.exp (-b/t)) = Real.Gamma a*b^(-a) := by
  have h := integral_comp_rpow_Ioi
    (fun u : ℝ => u^(a-1)*Real.exp (-b*u)) (show (-1:ℝ) ≠ 0 by norm_num)
  rw [laplace_rpow ha hb] at h
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have hp : t^(-a-1) = t^((-1:ℝ)-1)*(t^(-1:ℝ))^(a-1) := by
    rw [← Real.rpow_mul ht.le,← Real.rpow_add ht]
    congr 1
    ring
  rw [hp]
  simp only [abs_neg,abs_one,one_mul,Real.rpow_neg_one,smul_eq_mul]
  rw [show -b/t = -b*t⁻¹ by ring]
  ring

end CubicFirstMoment

end

end OAI
