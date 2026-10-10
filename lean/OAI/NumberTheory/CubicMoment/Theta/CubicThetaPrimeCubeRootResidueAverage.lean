import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootDilationFixed
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootResidueOverlap

namespace OAI

/-! The actual Hecke overlap forces a lower bound for the zero-frequency
component of the arithmetic residue on the cubic root cover. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRootResidue_average_pairing {p : Eisenstein} (hp : primaryPrime p) :
    inner ℂ (cubicThetaPrimeCubeRootFourierL2 hp 0
      (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2))
      (cubicThetaPrimeCubeRootDilationL2 hp cubicThetaArithmeticResidueL2)=
    (norm p:ℂ)⁻¹*(‖cubicThetaArithmeticResidueL2‖^2:ℂ) := by
  rw [cubicThetaPrimeCubeRootDilationL2_average_pairing,cubicThetaPrimeCubeRootResidue_overlap]

theorem cubicThetaPrimeCubeRootResidue_average_norm_lower {p : Eisenstein} (hp : primaryPrime p) :
    (norm p)⁻¹*‖cubicThetaArithmeticResidueL2‖≤
      ‖cubicThetaPrimeCubeRootFourierL2 hp 0
        (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)‖ := by
  let a := cubicThetaPrimeCubeRootFourierL2 hp 0
    (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)
  let b := cubicThetaPrimeCubeRootDilationL2 hp cubicThetaArithmeticResidueL2
  let n : ℝ := ‖cubicThetaArithmeticResidueL2‖
  have he := norm_inner_le_norm (𝕜:=ℂ) a b
  rw [cubicThetaPrimeCubeRootResidue_average_pairing,
    (cubicThetaPrimeCubeRootDilationL2 hp).norm_map] at he
  change ‖(norm p:ℂ)⁻¹*(n:ℂ)^2‖≤‖a‖*n at he
  rw [norm_mul,norm_inv,Complex.norm_of_nonneg (norm_nonneg p),norm_pow,
    Complex.norm_of_nonneg (_root_.norm_nonneg cubicThetaArithmeticResidueL2)] at he
  change (norm p)⁻¹*n≤‖a‖
  by_cases hn : n=0
  · rw [hn,mul_zero]
    exact _root_.norm_nonneg a
  · have hnpos : 0<n := lt_of_le_of_ne (_root_.norm_nonneg cubicThetaArithmeticResidueL2) (Ne.symm hn)
    apply (mul_le_mul_iff_of_pos_right hnpos).mp
    nlinarith [he]

theorem cubicThetaPrimeCubeRootResidue_average_mass_lower {p : Eisenstein} (hp : primaryPrime p) :
    (norm p)^2*‖cubicThetaPrimeCubeRootFourierL2 hp 0
      (cubicThetaPrimeCubeRootLiftL2 hp cubicThetaArithmeticResidueL2)‖^2≥
      ‖cubicThetaArithmeticResidueL2‖^2 := by
  have he := cubicThetaPrimeCubeRootResidue_average_norm_lower hp
  have hq : 0<norm p := norm_pos_of_ne_zero hp.2.ne_zero
  have hs := mul_le_mul_of_nonneg_left he hq.le
  rw [←mul_assoc,mul_inv_cancel₀ hq.ne',one_mul] at hs
  have ht := mul_self_le_mul_self (_root_.norm_nonneg cubicThetaArithmeticResidueL2) hs
  simpa only [←pow_two,mul_pow] using ht

end CubicFirstMoment

end

end OAI
