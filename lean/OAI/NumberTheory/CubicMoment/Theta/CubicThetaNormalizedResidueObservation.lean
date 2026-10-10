import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPoleRadialScaling

namespace OAI

/-! A common radial factor for the normalized local residue coordinates. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPoleScaling_normalization {a : Eisenstein} (ha : a≠0) :
    (norm a:ℂ)⁻¹*(‖(a:ℂ)‖:ℂ)^(4/3:ℂ)=(norm a:ℂ)^(-(1/3:ℂ)) := by
  have hr : 0<‖(a:ℂ)‖ := norm_pos_iff.mpr (fun he => ha (Subtype.ext he))
  have hq : 0<norm a := norm_pos_of_ne_zero ha
  have hn : norm a=‖(a:ℂ)‖^2 := Complex.normSq_eq_norm_sq _
  have hs (e : ℝ) : (‖(a:ℂ)‖^2)^e=‖(a:ℂ)‖^(2*e) := by
    rw [←Real.rpow_natCast ‖(a:ℂ)‖ 2,←Real.rpow_mul hr.le]
    norm_num
  have he : (norm a)⁻¹*‖(a:ℂ)‖^(4/3:ℝ)=(norm a)^(-(1/3:ℝ)) := by
    rw [hn,←Real.rpow_neg_one,hs,hs,←Real.rpow_add hr]
    norm_num
  have hR : (‖(a:ℂ)‖:ℂ)^(4/3:ℂ)=((‖(a:ℂ)‖^(4/3:ℝ):ℝ):ℂ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow hr.le (4/3:ℝ)).symm
  have hQ : (norm a:ℂ)^(-(1/3:ℂ))=(((norm a)^(-(1/3:ℝ)):ℝ):ℂ) := by
    simpa only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow hq.le (-(1/3:ℝ))).symm
  rw [hR,hQ,←Complex.ofReal_inv,←Complex.ofReal_mul,he]

theorem cubicThetaNormalizedResidue_observation_mul {a h : Eisenstein}
    (ha : a≠0) (hh : h≠0) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤2*‖(a:ℂ)‖,W v=0) :
    (norm a:ℂ)⁻¹*inner ℂ
        (cubicThetaCuspFourierTest (a*h)
          (cubicThetaRadialWeightScale ‖(a:ℂ)‖
            (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) W))
        (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))=
      ((Real.pi:ℂ)/Complex.Gamma (4/3)*cubicThetaFourierRadialTest h W (4/3))*
        ((norm a:ℂ)^(-(1/3:ℂ))*cubicThetaArithmeticFourierResidue (a*h) (4/3)) := by
  have he := cubicThetaResidue_fourier_observation (mul_ne_zero ha hh)
    (cubicThetaRadialWeightScale ‖(a:ℂ)‖
      (norm_pos_iff.mpr (fun he => ha (Subtype.ext he))) W)
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at he
  rw [he,cubicThetaPoleRadialTest_scale ha hh W hW]
  have hp := cubicThetaPoleScaling_normalization ha
  linear_combination
    ((Real.pi:ℂ)/Complex.Gamma (4/3)*cubicThetaFourierRadialTest h W (4/3)*
      cubicThetaArithmeticFourierResidue (a*h) (4/3))*hp

end CubicFirstMoment

end

end OAI
