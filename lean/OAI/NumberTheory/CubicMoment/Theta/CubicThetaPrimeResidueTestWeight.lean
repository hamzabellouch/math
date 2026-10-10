import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPoleRadialScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialRealPositive

namespace OAI

/-! A concrete high-cusp test with a nonzero common radial factor for
the three unramified residue coordinates. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialTestWeight_low {v : ℝ} (hv : v≤2) :
    cubicThetaRadialTestWeight v=0 := by
  change ((max 0 (1-|v-3|):ℝ):ℂ)=0
  rw [abs_of_nonpos (by linarith),max_eq_left (by linarith),Complex.ofReal_zero]

def cubicThetaPrimeResidueTestWeight {p : Eisenstein} (hp : primaryPrime p) : C_c(ℝ,ℂ) :=
  cubicThetaRadialWeightScale (‖(p:ℂ)‖^2)⁻¹
    (inv_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he)))))
    cubicThetaRadialTestWeight

lemma cubicThetaPrimeResidueTestWeight_low {p : Eisenstein} (hp : primaryPrime p)
    {v : ℝ} (hv : v≤2*‖(p:ℂ)‖^2) : cubicThetaPrimeResidueTestWeight hp v=0 := by
  change cubicThetaRadialTestWeight ((‖(p:ℂ)‖^2)⁻¹*v)=0
  apply cubicThetaRadialTestWeight_low
  rw [mul_comm,←div_eq_mul_inv,div_le_iff₀
    (sq_pos_of_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))))]
  exact hv

lemma cubicThetaPrimeResidueTestWeight_scale {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaRadialWeightScale ‖((p^2:Eisenstein):ℂ)‖
      (norm_pos_iff.mpr (fun he => (pow_ne_zero 2 hp.2.ne_zero) (Subtype.ext he)))
      (cubicThetaPrimeResidueTestWeight hp)=cubicThetaRadialTestWeight := by
  ext v
  change cubicThetaRadialTestWeight ((‖(p:ℂ)‖^2)⁻¹*(‖((p^2:Eisenstein):ℂ)‖*v))=_
  rw [Subalgebra.coe_pow,norm_pow,inv_mul_cancel_left₀
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))))]

theorem cubicThetaPrimeResidueTestWeight_radial_ne_zero {p : Eisenstein}
    (hp : primaryPrime p) {h : Eisenstein} (hh : h≠0) :
    cubicThetaFourierRadialTest h (cubicThetaPrimeResidueTestWeight hp) (4/3)≠0 := by
  have he := cubicThetaPoleRadialTest_scale (pow_ne_zero 2 hp.2.ne_zero) hh
    (cubicThetaPrimeResidueTestWeight hp) (by
      intro v hv
      apply cubicThetaPrimeResidueTestWeight_low hp
      simpa only [Subalgebra.coe_pow,norm_pow] using hv)
  rw [cubicThetaPrimeResidueTestWeight_scale hp] at he
  intro hz
  rw [hz,mul_zero] at he
  have hpos := cubicThetaFourierRadialTest_real_pos
    (mul_ne_zero (pow_ne_zero 2 hp.2.ne_zero) hh) (4/3)
  norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at hpos
  rw [he,Complex.zero_re] at hpos
  exact (lt_irrefl 0) hpos

end CubicFirstMoment

end

end OAI
