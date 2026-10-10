import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootDilationObservation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootAverageIdentity

namespace OAI

/-! Reading the saturated zero-frequency identity through actual cusp
observations, with the covering normalization cancelled. -/
noncomputable section
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRoot_observation_lift {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (u : cubicThetaGlobalEnergySpace) :
    cubicThetaPrimeCubeRootObservation hp h W
      (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaGlobalEnergyValueMap u))=
      ((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ)*
        inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaCuspRestriction u) := by
  change inner ℂ _ (cubicThetaPrimeCubeRootCuspRestriction hp _)=_
  rw [cubicThetaPrimeCubeRootCuspRestriction_lift,inner_smul_right]

theorem cubicThetaArithmeticResidue_average_observation {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) (hW : ∀ v≤2*‖(p:ℂ)‖^3,W v=0) :
    (norm p:ℂ)*inner ℂ (cubicThetaCuspFourierTest (p^3*h)
      (cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
        (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)) W))
      (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))=
    ((‖(p:ℂ)‖^3:ℝ):ℂ)^2*inner ℂ (cubicThetaCuspFourierTest h W)
      (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3))) := by
  let V := cubicThetaRadialWeightScale (‖(p:ℂ)‖^3)
    (lt_of_lt_of_le zero_lt_one (cubicThetaPrimeCube_height_one hp)) W
  have he := congrArg (cubicThetaPrimeCubeRootObservation hp (p^3*h) V)
    (cubicThetaArithmeticResidue_average_identity hp)
  have hk : Ideal.Quotient.mk (modulus (p^3)) (p^3*h)=0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem,modulus,Ideal.mem_span_singleton]
    exact dvd_mul_right (p^3) h
  rw [map_smul,cubicThetaPrimeCubeRoot_observation_projection,ite_eq_left hk] at he
  change (norm p:ℂ)*cubicThetaPrimeCubeRootObservation hp (p^3*h) V
    (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaGlobalEnergyValueMap
      (cubicThetaArithmeticResidueEnergy (4/3))))=
      cubicThetaPrimeCubeRootObservation hp (p^3*h) V
        (cubicThetaPrimeCubeRootDilationL2 hp (cubicThetaGlobalEnergyValueMap
          (cubicThetaArithmeticResidueEnergy (4/3)))) at he
  rw [cubicThetaPrimeCubeRoot_observation_lift,
    cubicThetaPrimeCubeRoot_observation_dilation hp h W hW] at he
  have hc : (((Real.sqrt ((cubicThetaPrimeCubeRootCoverGroup hp).index:ℝ))⁻¹:ℂ))≠0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (cubicThetaPrimeCubeRootCoverDegree_pos hp)).ne')
  apply mul_left_cancel₀ hc
  linear_combination he

end CubicFirstMoment

end

end OAI
