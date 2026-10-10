import OAI.NumberTheory.CubicMoment.Angular.AngularAlgebra
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

namespace OAI

/-! The exact numerical constant in the cubic Riesz integral. -/

noncomputable section
namespace CubicFirstMoment

lemma Gamma_third_mul_two_thirds :
    Real.Gamma (1/3:ℝ)*Real.Gamma (2/3:ℝ) = 2*Real.pi/Real.sqrt 3 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1/3:ℝ)
  norm_num at h
  rw [show Real.pi*(1/3:ℝ) = Real.pi/3 by ring,Real.sin_pi_div_three] at h
  convert h using 1
  ring

lemma cStar_sq : cStar^2 =
    (2*Real.pi)^(4/3:ℝ)/(9*(Real.Gamma (2/3:ℝ))^2) := by
  unfold cStar
  rw [div_pow,mul_pow,← Real.rpow_natCast ((2*Real.pi)^(2/3:ℝ)) 2,
    ← Real.rpow_mul (by positivity : 0 ≤ 2*Real.pi)]
  norm_num

/-- Includes the cubing multiplicity, trace-pairing dilation, and the
covolume-normalized planar measure. -/
theorem cubic_riesz_constant :
    (1/3:ℝ)*(2/Real.sqrt 3)*Real.pi*(2*Real.pi)^(-(2/3:ℝ))*
      Real.Gamma (1/3:ℝ)/Real.Gamma (2/3:ℝ) = cStar^2 := by
  have hg : Real.Gamma (2/3:ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hs : Real.sqrt (3:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hh : Real.Gamma (1/3:ℝ) =
      (2*Real.pi)/(Real.sqrt 3*Real.Gamma (2/3:ℝ)) := by
    apply (eq_div_iff (mul_ne_zero hs hg)).mpr
    have h := Gamma_third_mul_two_thirds
    apply (eq_div_iff hs).mp at h
    nlinarith [h]
  rw [hh,cStar_sq]
  have hr : (2*Real.pi)^2*(2*Real.pi)^(-(2/3:ℝ)) = (2*Real.pi)^(4/3:ℝ) := by
    rw [← Real.rpow_natCast (2*Real.pi) 2,← Real.rpow_add (by positivity : 0 < 2*Real.pi)]
    norm_num
  rw [← hr]
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

lemma cubic_riesz_gaussian_constant :
    (1/3:ℝ)*(2/Real.sqrt 3)*Real.pi*(4*Real.pi^2)^(-(1/3:ℝ))*
      Real.Gamma (1/3:ℝ)/Real.Gamma (2/3:ℝ) = cStar^2 := by
  have he : (4*Real.pi^2)^(-(1/3:ℝ)) = (2*Real.pi)^(-(2/3:ℝ)) := by
    rw [show 4*Real.pi^2 = (2*Real.pi)^2 by ring,
      ← Real.rpow_natCast (2*Real.pi) 2,← Real.rpow_mul (by positivity : 0 ≤ 2*Real.pi)]
    norm_num
  rw [he]
  exact cubic_riesz_constant

end CubicFirstMoment

end

end OAI
