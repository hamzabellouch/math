import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeEnergyValue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionEnergyInvolution

namespace OAI

/-! Geometric inversion on the actual automorphic mass completion. -/
noncomputable section
namespace CubicFirstMoment

local instance inversionMass_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

lemma cubicThetaInversionSmooth_mass_norm (F : cubicThetaSmoothTests) :
    ‖cubicThetaGlobalMassClosure (cubicThetaInversionSmooth F)‖=
      ‖cubicThetaGlobalMassClosure F‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  exact cubicThetaInversion_test_mass_norm F

def cubicThetaInversionMass : cubicThetaAutomorphicL2 →ₗᵢ[ℂ] cubicThetaAutomorphicL2 :=
  (cubicThetaGlobalMassClosure.comp cubicThetaInversionSmoothLinear).extendOfIsometry
    cubicThetaGlobalMassClosure_dense cubicThetaInversionSmooth_mass_norm

lemma cubicThetaInversionMass_smooth (F : cubicThetaSmoothTests) :
    cubicThetaInversionMass (cubicThetaGlobalMassClosure F)=
      cubicThetaGlobalMassClosure (cubicThetaInversionSmooth F) :=
  LinearMap.extendOfIsometry_eq _ _ _ F

theorem cubicThetaInversionMass_involutive (u : cubicThetaAutomorphicL2) :
    cubicThetaInversionMass (cubicThetaInversionMass u)=u := by
  refine cubicThetaGlobalMassClosure_dense.induction_on u
    (isClosed_eq (cubicThetaInversionMass.continuous.comp
      cubicThetaInversionMass.continuous) continuous_id) ?_
  intro F
  rw [cubicThetaInversionMass_smooth,cubicThetaInversionMass_smooth,
    cubicThetaInversionSmooth_involutive]

theorem cubicThetaInversionMass_energy (u : cubicThetaGlobalEnergySpace) :
    cubicThetaInversionMass (cubicThetaGlobalEnergyValueMap u)=
      cubicThetaGlobalEnergyValueMap (cubicThetaInversionEnergy u) := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq (cubicThetaInversionMass.continuous.comp
      cubicThetaGlobalEnergyValueMap.continuous)
      (cubicThetaGlobalEnergyValueMap.continuous.comp cubicThetaInversionEnergy.continuous)) ?_
  intro F
  change cubicThetaInversionMass (cubicThetaGlobalEnergyValueMap (cubicThetaGlobalEnergyTest F))=
    cubicThetaGlobalEnergyValueMap (cubicThetaInversionEnergy (cubicThetaGlobalEnergyTest F))
  rw [cubicThetaGlobalEnergyValueMap_test,cubicThetaInversionMass_smooth,
    cubicThetaInversionEnergy_test,cubicThetaGlobalEnergyValueMap_test]

end CubicFirstMoment

end

end OAI
