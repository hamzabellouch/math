import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramIntegralDecomposition
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierProfileNorm

namespace OAI

/-! Scaling of the actual identity row of the positive Gram formula. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaHorizontalFourier_character_scale (a h k : Eisenstein) (ha : a≠0) :
    cubicThetaHorizontalFourierCoefficient (a*h) (cubicThetaHorizontalCharacter (a*k))=
      cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter k) := by
  by_cases hh : h=k
  · subst k
    rw [cubicThetaHorizontalFourier_character_self,cubicThetaHorizontalFourier_character_self]
  · have hm : a*h≠a*k := fun he => hh (mul_left_cancel₀ ha he)
    rw [cubicThetaHorizontalFourier_character_zero hm,cubicThetaHorizontalFourier_character_zero hh]

theorem cubicThetaGramIdentityPart_scale (a h k : Eisenstein) (ha : a≠0)
    (W V : C_c(ℝ,ℂ)) (ε : ℝ) :
    cubicThetaGramIdentityPart (a*h) (a*k)
      (cubicThetaRadialWeightScale ‖(a:ℂ)‖
        (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) W)
      (cubicThetaRadialWeightScale ‖(a:ℂ)‖
        (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) V)
      (ε/‖(a:ℂ)‖)=(norm a:ℂ)*cubicThetaGramIdentityPart h k W V ε := by
  let r := ‖(a:ℂ)‖
  have hr : 0<r := norm_pos_iff.mpr (fun he => ha (Subtype.ext he))
  have hN : norm a=r^2 := Complex.normSq_eq_norm_sq _
  let C := cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter k)
  let f : ℝ → ℂ := fun v => star (W v)/(v:ℂ)^3*(V v*C)
  have he (v : ℝ) : star (W (r*v))/(v:ℂ)^3*(V (r*v)*C)=(r:ℂ)^3*f (r*v) := by
    dsimp only [f]
    rw [Complex.ofReal_mul,mul_pow]
    have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
    by_cases hv : v=0
    · simp only [hv,Complex.ofReal_zero,zero_pow (by decide : 3≠0),div_zero,mul_zero,zero_mul]
    · have hvC : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv
      field_simp
  unfold cubicThetaGramIdentityPart
  rw [cubicThetaHorizontalFourier_character_scale _ _ _ ha]
  change (∫ v in Ioi (ε/r),star (W (r*v))/(v:ℂ)^3*(V (r*v)*C))=(norm a:ℂ)*∫ v in Ioi ε,f v
  simp_rw [he]
  rw [integral_const_mul,integral_comp_mul_left_Ioi f (ε/r) hr]
  have hε : r*(ε/r)=ε := by field_simp
  rw [hε,Complex.real_smul,hN,Complex.ofReal_pow,Complex.ofReal_inv]
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  field_simp

end CubicFirstMoment

end

end OAI
