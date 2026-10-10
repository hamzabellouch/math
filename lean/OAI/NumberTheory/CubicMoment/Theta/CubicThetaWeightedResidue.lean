import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticCriticalImage
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimePoleFactors

namespace OAI

/-! Unramified coefficient laws for the actual arithmetic residue in
the Whittaker normalization. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaWeightedFourierResidue (h : Eisenstein) : ℂ :=
  (norm h:ℂ)^(-(1/3:ℂ))*cubicThetaArithmeticFourierResidue h (4/3)

lemma cubicThetaWeightedFourierResidue_prime {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaWeightedFourierResidue (p*h)=
      (cubicSymbol p h*star (gauss p)/(Real.sqrt (norm p):ℂ))*
        cubicThetaWeightedFourierResidue h := by
  have hc := hp.2.coprime_iff_not_dvd.mpr hh
  have he := (cubicThetaPrimeResidueVector_line_iff_cube hp h hh).mpr
    (cubicThetaArithmeticFourierResidue_cube hp h (fun hz => hh (hz ▸ dvd_zero p)))
  change cubicThetaPrimeCriticalScale p*cubicThetaArithmeticFourierResidue (p*h) (4/3)=
    (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*
      cubicThetaArithmeticFourierResidue h (4/3) at he
  rw [cubicThetaPrimeAdditiveGauss_two hp h hc,cubicThetaPrimeAdditiveGauss_one hp h hc,
    star_mul,star_mul,star_star] at he
  have hs : star (Real.sqrt (norm p):ℂ)=(Real.sqrt (norm p):ℂ) := by simp
  rw [hs] at he
  have hn : (norm p:ℂ)=(Real.sqrt (norm p):ℂ)^2 := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt (norm_nonneg p)]
  have hs0 : (Real.sqrt (norm p):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (norm_pos_of_ne_zero hp.2.ne_zero)).ne'
  have hnorm : (norm (p*h):ℂ)^(-(1/3:ℂ))=
      (norm p:ℂ)^(-(1/3:ℂ))*(norm h:ℂ)^(-(1/3:ℂ)) := by
    rw [norm_mul_eq,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg p) (norm_nonneg h)]
  unfold cubicThetaWeightedFourierResidue
  rw [hnorm]
  calc
    _ = (norm h:ℂ)^(-(1/3:ℂ))*(cubicThetaPrimeCriticalScale p*
        cubicThetaArithmeticFourierResidue (p*h) (4/3)) := by
      unfold cubicThetaPrimeCriticalScale
      ring
    _ = _ := by
      rw [he,hn]
      field_simp

lemma cubicThetaWeightedFourierResidue_square_zero {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) : cubicThetaWeightedFourierResidue (p^2*h)=0 := by
  rw [cubicThetaWeightedFourierResidue,cubicThetaArithmeticFourierResidue_square_zero hp h hh,mul_zero]

lemma cubicThetaNorm_cube_cpow (a : Eisenstein) :
    (norm (a^3):ℂ)^(-(1/3:ℂ))=(norm a:ℂ)⁻¹ := by
  have hcast : ((norm a^3:ℝ):ℂ)^(-(1/3:ℂ))=((norm a^3)^(-(1/3:ℝ)):ℝ) := by
    simpa only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow (pow_nonneg (norm_nonneg a) 3) (-(1/3:ℝ))).symm
  rw [eisenstein_norm_pow,hcast,←Complex.ofReal_inv]
  congr 1
  rw [←Real.rpow_natCast (norm a) 3,←Real.rpow_mul (norm_nonneg a)]
  norm_num [Real.rpow_neg_one]

lemma cubicThetaWeightedFourierResidue_cube {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : h≠0) :
    cubicThetaWeightedFourierResidue (p^3*h)=
      (norm p:ℂ)⁻¹*cubicThetaWeightedFourierResidue h := by
  unfold cubicThetaWeightedFourierResidue
  rw [norm_mul_eq,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (norm_nonneg (p^3)) (norm_nonneg h),cubicThetaNorm_cube_cpow,
    cubicThetaArithmeticFourierResidue_cube hp h hh]
  ring

end CubicFirstMoment

end

end OAI
