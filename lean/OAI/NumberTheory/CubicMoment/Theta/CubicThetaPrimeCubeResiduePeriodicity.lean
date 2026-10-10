import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootAverageObservation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeResidueTestWeight
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramCubeResidueBound

namespace OAI

/-! Cubic periodicity of the actual arithmetic Fourier residues follows
from the saturated finite-cover averaging identity. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaArithmeticFourierResidue_cube {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : h≠0) :
    cubicThetaArithmeticFourierResidue (p^3*h) (4/3)=
      cubicThetaArithmeticFourierResidue h (4/3) := by
  let W := cubicThetaPrimeCubeResidueTestWeight hp
  let V := cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
    (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)) W
  have hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0 := fun _ hv => cubicThetaPrimeCubeResidueTestWeight_low hp hv
  have he := cubicThetaArithmeticResidue_average_observation hp h W hW
  have h3 := cubicThetaResidue_fourier_observation (mul_ne_zero (pow_ne_zero 3 hp.2.ne_zero) hh)
    V (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  have h0 := cubicThetaResidue_fourier_observation hh W (σ:=(4/3:ℝ)) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at h3 h0
  have hscale : cubicThetaFourierRadialTest (p^3*h) V (4/3)=
      (norm p:ℂ)^2*cubicThetaFourierRadialTest h W (4/3) := by
    have hs := cubicThetaPoleRadialTest_scale (pow_ne_zero 3 hp.2.ne_zero) hh W (by
      intro v hv
      apply hW v
      simpa only [Subalgebra.coe_pow,norm_pow] using hv)
    rw [cubicThetaPrimeCube_pole_scale hp] at hs
    simpa only [Subalgebra.coe_pow,norm_pow] using hs
  have hn : ((‖(p:ℂ)‖^3:ℝ):ℂ)^2=(norm p:ℂ)^3 := by
    rw [show norm p=‖(p:ℂ)‖^2 from Complex.normSq_eq_norm_sq _,Complex.ofReal_pow,Complex.ofReal_pow]
    ring
  change (norm p:ℂ)*inner ℂ (cubicThetaCuspFourierTest (p^3*h) V)
    (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))=_ at he
  rw [h3,h0,hscale,hn] at he
  have hf : (norm p:ℂ)^3*((Real.pi:ℂ)/Complex.Gamma (4/3))*
      cubicThetaFourierRadialTest h W (4/3)≠0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne')
      · exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero)
          (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
    · exact cubicThetaPrimeCubeResidueTestWeight_radial_ne_zero hp hh
  apply mul_left_cancel₀ hf
  linear_combination he

end CubicFirstMoment

end

end OAI
