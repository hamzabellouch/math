import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoefficientConjugation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMellinReciprocity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConjugateProjection

namespace OAI

/-! The actual base scalar is real. This uses exact conjugation of the
arithmetic series and its proved inversion law; it does not set the scalar
or its absolute value equal to one. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaArithmetic_axis_term_star (n : Eisenstein) (v : ℝ) :
    star (cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v n) =
      cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v (conjugate n) := by
  by_cases hn : n = 0
  · simp [hn,cubicThetaSeriesTerm]
  · have hc : conjugate n ≠ 0 := fun h => hn (conjugate.injective (h.trans (map_zero conjugate).symm))
    have hf : ‖cubicThetaFrequency (conjugate n)‖ = ‖cubicThetaFrequency n‖ := by
      simp only [cubicThetaFrequency,norm_div,conjugate_coe,norm_star]
    simp only [cubicThetaSeriesTerm,hn,hc,ite_false,
      cubicThetaArithmeticCoefficient_conjugate,hf,tracePair,mul_zero,
      Complex.zero_re,mul_zero,AddChar.map_zero_eq_one,Circle.coe_one,mul_one,
      star_mul,cubicThetaWhittaker_star]
    ring

lemma cubicThetaArithmeticAxis_star (v : ℝ) :
    star (cubicThetaArithmeticAxis v) = cubicThetaArithmeticAxis v := by
  unfold cubicThetaArithmeticAxis cubicThetaNonconstant
  rw [tsum_star]
  calc
    _ = ∑' n : Eisenstein,
        cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v (conjugate n) :=
      tsum_congr (fun n => cubicThetaArithmetic_axis_term_star n v)
    _ = _ := conjugate.toEquiv.tsum_eq _

lemma cubicThetaSeriesConstant_star : star cubicThetaSeriesConstant = cubicThetaSeriesConstant := by
  let d : ℝ := (2:ℝ)^(-(2/3:ℝ))-(2:ℝ)^(2/3:ℝ)
  have hd : d < 0 := sub_neg.mpr (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num))
  have hd0 : (d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne
  have he := cubicThetaArithmeticAxis_small (v:=2) (by norm_num)
  have hp : ((2:ℂ)^(-(2/3:ℂ))-(2:ℂ)^(2/3:ℂ)) = (d:ℂ) := by
    rw [Complex.ofReal_sub,Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2),
      Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2)]
    norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat]
  norm_num only [Complex.ofReal_ofNat] at he
  rw [hp] at he
  have hs := congrArg star he
  simp only [star_add,star_mul,cubicThetaArithmeticAxis_star,
    Complex.star_def,Complex.conj_ofReal] at hs
  apply mul_right_cancel₀ hd0
  simpa only [←Complex.star_def,mul_comm] using add_left_cancel (hs.symm.trans he)

theorem cubicThetaArithmeticBaseScalar_star :
    star cubicThetaArithmeticBaseScalar = cubicThetaArithmeticBaseScalar := by
  have hC : (cubicThetaConstant:ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    unfold cubicThetaConstant
    positivity
  have he := cubicThetaSeriesConstant_star
  rw [cubicThetaSeriesConstant,star_div₀,Complex.star_def,Complex.conj_ofReal] at he
  have hb := cubicThetaArithmeticBaseScalar_ne_zero
  have hx := (div_eq_div_iff (star_ne_zero.mpr hb) hb).mp he
  exact (mul_left_cancel₀ hC hx).symm

end CubicFirstMoment

end

end OAI
