import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueWhittaker

namespace OAI

/-! Scaling of the literal Fourier frequency and cubic-pole radial factor. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRowFrequency_mul (a h : Eisenstein) :
    cubicThetaRowFrequency (a*h)=(a:ℂ)*cubicThetaRowFrequency h := by
  unfold cubicThetaRowFrequency
  push_cast
  ring

lemma cubicThetaRowFrequency_norm_mul (a h : Eisenstein) :
    ‖cubicThetaRowFrequency (a*h)‖=‖(a:ℂ)‖*‖cubicThetaRowFrequency h‖ := by
  rw [cubicThetaRowFrequency_mul,norm_mul]

lemma cubicThetaRowHeatScale_mul (a h : Eisenstein) :
    cubicThetaRowHeatScale (a*h)=‖(a:ℂ)‖^2*cubicThetaRowHeatScale h := by
  unfold cubicThetaRowHeatScale
  rw [cubicThetaRowFrequency_mul,Complex.normSq_mul,Complex.normSq_eq_norm_sq (a:ℂ)]
  ring

lemma cubicThetaPoleFactor_mul {a h : Eisenstein} (ha : a≠0) (hh : h≠0) :
    2*(cubicThetaRowHeatScale (a*h))^(1/6:ℝ)/‖cubicThetaRowFrequency (a*h)‖=
      ‖(a:ℂ)‖^(-(2/3:ℝ))*(2*(cubicThetaRowHeatScale h)^(1/6:ℝ)/‖cubicThetaRowFrequency h‖) := by
  have hr : 0<‖(a:ℂ)‖ := norm_pos_iff.mpr (fun he => ha (Subtype.ext he))
  have hq : 0<‖cubicThetaRowFrequency h‖ := norm_pos_iff.mpr (by
    unfold cubicThetaRowFrequency
    exact div_ne_zero (fun he => hh (Subtype.ext he)) (mul_ne_zero (by norm_num) traceLambda_ne_zero))
  have hp : (‖(a:ℂ)‖^2)^(1/6:ℝ)=‖(a:ℂ)‖^(1/3:ℝ) := by
    rw [←Real.rpow_natCast ‖(a:ℂ)‖ 2,←Real.rpow_mul hr.le]
    norm_num
  have he : ‖(a:ℂ)‖^(-(2/3:ℝ))*‖(a:ℂ)‖=‖(a:ℂ)‖^(1/3:ℝ) := by
    calc
      _ = ‖(a:ℂ)‖^(-(2/3:ℝ))*‖(a:ℂ)‖^(1:ℝ) := by rw [Real.rpow_one]
      _ = ‖(a:ℂ)‖^(-(2/3:ℝ)+1) := (Real.rpow_add hr _ _).symm
      _ = _ := by norm_num
  rw [cubicThetaRowHeatScale_mul,cubicThetaRowFrequency_norm_mul,
    Real.mul_rpow (sq_nonneg _) (cubicThetaRowHeatScale_pos hh).le,hp]
  rw [←he]
  have halg (r q b A : ℝ) (hr : r≠0) (hq : q≠0) :
      2*(b*r*A)/(r*q)=b*(2*A/q) := by field_simp
  exact halg _ _ _ _ hr.ne' hq.ne'

end CubicFirstMoment

end

end OAI
