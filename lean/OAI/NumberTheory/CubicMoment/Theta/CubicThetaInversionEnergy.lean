import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionSmooth
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyIntegralIdentities
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalLocalRellich

namespace OAI

/-! The geometric inversion extends isometrically to the actual
completed automorphic energy space. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
local instance : AddCommGroup cubicThetaSmoothTests := Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaInversionSmoothLinear : cubicThetaSmoothTests →ₗ[ℂ] cubicThetaSmoothTests where
  toFun := cubicThetaInversionSmooth
  map_add' _F _G := rfl
  map_smul' _c _F := rfl

lemma cubicThetaInversion_quotient_energy (F : cubicThetaSmoothTests) (q : CubicThetaQuotient) :
    cubicThetaQuotientEnergy (cubicThetaInversionSmooth F) q=
      cubicThetaQuotientEnergy F (cubicThetaIntegralQuotientMap cubicThetaFullInversion q) := by
  obtain ⟨p,rfl⟩ := cubicThetaQuotientMap_surjective q
  rw [cubicThetaQuotientEnergy_apply,cubicThetaIntegralQuotientMap_apply,cubicThetaQuotientEnergy_apply]
  exact cubicThetaInversionSection_energy F p

lemma cubicThetaInversion_test_mass_norm (F : cubicThetaSmoothTests) :
    ‖cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest (cubicThetaInversionSmooth F))‖^2=
      ‖cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)‖^2 := by
  rw [cubicThetaGlobalInclusion_test_norm_sq,cubicThetaGlobalInclusion_test_norm_sq]
  calc
    _ = ∫ q, cubicThetaSectionNorm F
        (cubicThetaIntegralQuotientMap cubicThetaFullInversion q)^2 ∂cubicThetaQuotientMeasure := by
      apply integral_congr_ae
      filter_upwards with q
      exact congrArg (fun x : ℝ => x^2) (cubicThetaInversionSection_norm F q)
    _ = _ := (cubicThetaIntegralQuotient_measurePreserving cubicThetaFullInversion).integral_comp
      (cubicThetaIntegralQuotientHomeomorph cubicThetaFullInversion).measurableEmbedding
      (fun q => cubicThetaSectionNorm F q^2)

lemma cubicThetaInversion_test_gradient_norm (F : cubicThetaSmoothTests) :
    ‖cubicThetaGlobalEnergyGradient (cubicThetaGlobalEnergyTest (cubicThetaInversionSmooth F))‖^2=
      ‖cubicThetaGlobalEnergyGradient (cubicThetaGlobalEnergyTest F)‖^2 := by
  rw [cubicThetaGlobalGradient_test_norm_sq,cubicThetaGlobalGradient_test_norm_sq]
  calc
    _ = ∫ q, cubicThetaQuotientEnergy F
        (cubicThetaIntegralQuotientMap cubicThetaFullInversion q) ∂cubicThetaQuotientMeasure := by
      apply integral_congr_ae
      filter_upwards with q
      exact cubicThetaInversion_quotient_energy F q
    _ = _ := (cubicThetaIntegralQuotient_measurePreserving cubicThetaFullInversion).integral_comp
      (cubicThetaIntegralQuotientHomeomorph cubicThetaFullInversion).measurableEmbedding
      (cubicThetaQuotientEnergy F)

lemma cubicThetaInversion_test_norm (F : cubicThetaSmoothTests) :
    ‖cubicThetaGlobalEnergyTest (cubicThetaInversionSmooth F)‖=‖cubicThetaGlobalEnergyTest F‖ := by
  apply (sq_eq_sq₀ (_root_.norm_nonneg _) (_root_.norm_nonneg _)).mp
  rw [cubicThetaGlobalEnergy_norm_sq,cubicThetaGlobalEnergy_norm_sq,
    cubicThetaInversion_test_mass_norm,cubicThetaInversion_test_gradient_norm]

def cubicThetaInversionEnergy : cubicThetaGlobalEnergySpace →ₗᵢ[ℂ] cubicThetaGlobalEnergySpace :=
  (cubicThetaGlobalEnergyTestLinear.comp cubicThetaInversionSmoothLinear).extendOfIsometry
    cubicThetaGlobalEnergyTestLinear_dense cubicThetaInversion_test_norm

lemma cubicThetaInversionEnergy_test (F : cubicThetaSmoothTests) :
    cubicThetaInversionEnergy (cubicThetaGlobalEnergyTest F)=
      cubicThetaGlobalEnergyTest (cubicThetaInversionSmooth F) :=
  LinearMap.extendOfIsometry_eq _ _ _ F

end CubicFirstMoment

end

end OAI
