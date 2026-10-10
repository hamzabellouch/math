import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootDilationObservation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeResidueTestWeight

namespace OAI

/-! A high radial test adapted to the cubic dilation. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaPrimeCubeResidueTestWeight {p : Eisenstein} (hp : primaryPrime p) : C_c(ℝ,ℂ) :=
  cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)⁻¹
    (inv_pos.mpr (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)))
    cubicThetaRadialTestWeight

lemma cubicThetaPrimeCubeResidueTestWeight_low {p : Eisenstein} (hp : primaryPrime p)
    {v : ℝ} (hv : v≤2*‖(p:ℂ)‖^3) : cubicThetaPrimeCubeResidueTestWeight hp v=0 := by
  change cubicThetaRadialTestWeight ((‖(p:ℂ)‖^3)⁻¹*v)=0
  apply cubicThetaRadialTestWeight_low
  rw [mul_comm,←div_eq_mul_inv,div_le_iff₀
    (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp))]
  exact hv

lemma cubicThetaPrimeCubeResidueTestWeight_scale {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
      (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp))
      (cubicThetaPrimeCubeResidueTestWeight hp)=cubicThetaRadialTestWeight := by
  ext v
  change cubicThetaRadialTestWeight ((‖(p:ℂ)‖^3)⁻¹*(‖(p:ℂ)‖^3*v))=_
  rw [inv_mul_cancel_left₀ (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)).ne']

lemma cubicThetaPrimeCubeResidueTestWeight_radial_ne_zero {p : Eisenstein} (hp : primaryPrime p)
    {h : Eisenstein} (hh : h≠0) :
    cubicThetaFourierRadialTest h (cubicThetaPrimeCubeResidueTestWeight hp) (4/3)≠0 := by
  have he := cubicThetaPoleRadialTest_scale (pow_ne_zero 3 hp.2.ne_zero) hh
    (cubicThetaPrimeCubeResidueTestWeight hp) (by
      intro v hv
      apply cubicThetaPrimeCubeResidueTestWeight_low hp
      simpa only [Subalgebra.coe_pow,norm_pow] using hv)
  simp only [Subalgebra.coe_pow,norm_pow] at he
  rw [cubicThetaPrimeCubeResidueTestWeight_scale hp] at he
  intro hz
  rw [hz,mul_zero] at he
  have hpos := cubicThetaFourierRadialTest_real_pos
    (mul_ne_zero (pow_ne_zero 3 hp.2.ne_zero) hh) (4/3)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hpos
  rw [he,Complex.zero_re] at hpos
  exact (lt_irrefl 0) hpos

end CubicFirstMoment

end

end OAI
