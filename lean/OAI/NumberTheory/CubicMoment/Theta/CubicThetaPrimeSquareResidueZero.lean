import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootObservationProjection
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootCuspLift
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootCriticalSquare
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeResidueTestWeight

namespace OAI

/-! The vanishing square projection is a vanishing of the actual
arithmetic Fourier residue, via a nonzero positive radial test. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaArithmeticFourierResidue_square_zero {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaArithmeticFourierResidue (p^2*h) (4/3)=0 := by
  have hh0 : h≠0 := fun he => hh (he ▸ dvd_zero p)
  have hk0 : p^2*h≠0 := mul_ne_zero (pow_ne_zero 2 hp.2.ne_zero) hh0
  have hz := congrArg (cubicThetaPrimeCubeRootObservation hp (p^2*h) cubicThetaRadialTestWeight)
    (cubicThetaArithmeticResidue_square_projection_zero hp h hh)
  rw [map_zero,cubicThetaPrimeCubeRoot_observation_projection,ite_eq_left rfl] at hz
  change inner ℂ (cubicThetaCuspFourierTest (p^2*h) cubicThetaRadialTestWeight)
    (cubicThetaPrimeCubeRootCuspRestriction hp
      (cubicThetaPrimeCubeRootLiftL2 hp
        (cubicThetaGlobalEnergyValueMap (cubicThetaArithmeticResidueEnergy (4/3)))))=0 at hz
  rw [cubicThetaPrimeCubeRootCuspRestriction_lift,inner_smul_right] at hz
  have hc : (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ))≠0 := by
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (cubicThetaPrimeCubeRootCoverDegree_pos hp)).ne')
  have ho := (mul_eq_zero.mp hz).resolve_left hc
  have he := cubicThetaResidue_fourier_observation hk0 cubicThetaRadialTestWeight
    (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at he
  rw [ho] at he
  have hrad : cubicThetaFourierRadialTest (p^2*h) cubicThetaRadialTestWeight (4/3)≠0 := by
    have hp := cubicThetaFourierRadialTest_real_pos hk0 (4/3)
    norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hp
    intro hz
    rw [hz,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have hgamma : (Real.pi:ℂ)/Complex.Gamma (4/3)≠0 :=
    div_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right hrad)).resolve_left hgamma

end CubicFirstMoment

end

end OAI
