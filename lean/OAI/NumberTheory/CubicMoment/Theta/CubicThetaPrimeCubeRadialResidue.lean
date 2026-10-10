import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialMellin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRadialPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaThetaObservation

namespace OAI

/-! The known constant term of the arithmetic residue transforms by the
critical cubed-prime multiplier under every admissible compact radial test. -/
noncomputable section
open Set
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPrimeCube_mellin_multiplier {p : Eisenstein} (hp : primaryPrime p) :
    (((‖(p:ℂ)‖^3:ℝ):ℂ)^2*((‖(p:ℂ)‖^3)⁻¹:ℝ)^(4/3:ℂ)+
      ((‖(p:ℂ)‖^3:ℝ):ℂ)^(4/3:ℂ))=(norm p)^2+norm p := by
  let u := ‖(p:ℂ)‖
  have hu : 0<u := norm_pos_iff.mpr (fun hz => hp.2.ne_zero (Subtype.ext hz))
  have hpw : (u^3)^(4/3:ℝ)=u^4 := by
    rw [←Real.rpow_natCast u 3,←Real.rpow_mul hu.le]
    norm_num
  have hr : (u^3)^2*((u^3)⁻¹)^(4/3:ℝ)+(u^3)^(4/3:ℝ)=(norm p)^2+norm p := by
    rw [Real.inv_rpow (pow_nonneg hu.le 3),hpw]
    change (u^3)^2*(u^4)⁻¹+u^4=(Complex.normSq (p:ℂ))^2+Complex.normSq (p:ℂ)
    rw [Complex.normSq_eq_norm_sq]
    change (u^3)^2*(u^4)⁻¹+u^4=(u^2)^2+u^2
    field_simp
    ring
  change ((u^3:ℝ):ℂ)^2*((u^3)⁻¹:ℝ)^(4/3:ℂ)+((u^3:ℝ):ℂ)^(4/3:ℂ)=_
  have he : (4/3:ℂ)=((4/3:ℝ):ℂ) := by norm_num
  rw [he,←Complex.ofReal_cpow (inv_nonneg.mpr (pow_nonneg hu.le 3)),
    ←Complex.ofReal_cpow (pow_nonneg hu.le 3)]
  exact_mod_cast hr

lemma cubicThetaPrimeCube_zeroRadialTest {p : Eisenstein} (hp : primaryPrime p)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0) :
    cubicThetaZeroRadialTest (cubicThetaRadialHeckeWeight (‖(p:ℂ)‖^3)
      (by have := cubicThetaPrimeCube_height_ge_one hp; linarith) W) (4/3)=
      ((norm p)^2+norm p:ℂ)*cubicThetaZeroRadialTest W (4/3) := by
  let r := ‖(p:ℂ)‖^3
  have hr1 : 1≤r := cubicThetaPrimeCube_height_ge_one hp
  have hr : 0<r := by linarith
  have hW2 : ∀ v≤(2:ℝ),W v=0 := by
    intro v hv
    apply hW
    change v≤2*r
    linarith
  have hA : ∀ v≤(2:ℝ),cubicThetaRadialWeightScale r⁻¹ (inv_pos.mpr hr) W v=0 := by
    intro v hv
    change W (r⁻¹*v)=0
    apply hW
    change r⁻¹*v≤2*r
    rw [mul_comm,←div_eq_mul_inv,div_le_iff₀ hr]
    have : 1≤r*r := by nlinarith
    nlinarith
  have hB : ∀ v≤(2:ℝ),cubicThetaRadialWeightScale r hr W v=0 := by
    intro v hv
    change W (r*v)=0
    apply hW
    change r*v≤2*r
    nlinarith
  rw [cubicThetaZeroRadialTest_hecke r hr W hW2 hA hB,
    cubicThetaPrimeCube_mellin_multiplier hp]

theorem cubicThetaPrimeCube_residue_radial_observation {p : Eisenstein} (hp : primaryPrime p)
    (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0) :
    inner ℂ (cubicThetaCuspFourierTest 0 W)
      (cubicThetaCuspRestriction (cubicThetaPrimeCubeHeckeEnergy hp
        (cubicThetaArithmeticResidueEnergy (4/3))))=
      ((norm p)^2+norm p:ℂ)*inner ℂ (cubicThetaCuspFourierTest 0 W)
        (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3))) := by
  have hW2 : ∀ v≤(2:ℝ),W v=0 := by
    intro v hv
    apply hW
    have := cubicThetaPrimeCube_height_ge_one hp
    nlinarith
  rw [cubicThetaPrimeCubeRadialPairing_energy hp _ W hW,
    cubicThetaResidue_zero_observation _ (cubicThetaPrimeCubeRadialWeight_low hp W hW),
    cubicThetaPrimeCube_zeroRadialTest hp W hW,cubicThetaResidue_zero_observation W hW2]
  ring

end CubicFirstMoment

end

end OAI
