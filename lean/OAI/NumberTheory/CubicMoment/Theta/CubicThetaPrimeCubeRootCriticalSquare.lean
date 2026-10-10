import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootNormBalance
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootResidueAverage

namespace OAI

/-! Positivity and the actual Hecke overlap force the missing square
frequency to vanish for the arithmetic residue. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticResidue_square_projection_zero {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaPrimeCubeRootFourierL2 hp
      (Ideal.Quotient.mk (modulus (p^3)) (p^2*h))
      (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)=0 := by
  have he := cubicThetaPrimeCubeRoot_norm_balance hp h hh cubicThetaArithmeticResidueL2
  have hlo := cubicThetaPrimeCubeRootResidue_average_mass_lower hp
  have hq : 1<norm p := cubicThetaPrimaryPrime_norm_gt_one hp
  have hpos : 0<(norm p)^3-(norm p)^2 := by
    have ht := mul_pos (sq_pos_of_pos (lt_trans zero_lt_one hq)) (sub_pos.mpr hq)
    nlinarith
  have hz : ‖cubicThetaPrimeCubeRootFourierL2 hp
      (Ideal.Quotient.mk (modulus (p^3)) (p^2*h))
      (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)‖^2=0 := by
    have hp : ((norm p)^3-(norm p)^2)*‖cubicThetaPrimeCubeRootFourierL2 hp
      (Ideal.Quotient.mk (modulus (p^3)) (p^2*h))
      (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)‖^2≤0 := by linarith
    apply le_antisymm ?_ (sq_nonneg _)
    by_contra hn
    have ht := mul_pos hpos (lt_of_not_ge hn)
    linarith
  apply norm_eq_zero.mp
  nlinarith [hz]

theorem cubicThetaArithmeticResidue_unit_correlation {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootUnitCorrelation hp cubicThetaArithmeticResidueL2=
      (‖cubicThetaArithmeticResidueL2‖^2:ℂ)/(norm p:ℂ)^2 := by
  have h1 : ¬p∣(1:Eisenstein) := fun hd => hp.2.not_isUnit (isUnit_iff_dvd_one.mpr hd)
  have he := cubicThetaPrimeCubeRoot_square_norm_identity hp 1 h1 cubicThetaArithmeticResidueL2
  rw [cubicThetaArithmeticResidue_square_projection_zero hp 1 h1,norm_zero,Complex.ofReal_zero,
    zero_pow (by decide : 2≠0),mul_zero] at he
  apply (eq_div_iff (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr
    (norm_pos_of_ne_zero hp.2.ne_zero).ne'))).mpr
  linear_combination he

end CubicFirstMoment

end

end OAI
