import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionFiniteEnergy

namespace OAI

/-! The geometric inversion on finite-energy sections agrees with the
already constructed involution on the completed global energy space. -/
noncomputable section
namespace CubicFirstMoment

local instance inversionFinite_addGroup : AddCommGroup cubicThetaFiniteEnergySections :=
  Module.addCommMonoidToAddCommGroup ℂ

def cubicThetaInversionRawEnergy : cubicThetaFiniteEnergySections →ₗ[ℂ] cubicThetaGlobalEnergySpace :=
  cubicThetaFiniteEnergyEmbedding.comp cubicThetaInversionFiniteLinear

def cubicThetaInversionFiniteExtension :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    cubicThetaInversionRawEnergy cubicThetaFiniteEnergyEmbedding

lemma cubicThetaInversionRawEnergy_bound (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaInversionRawEnergy F‖≤1*‖cubicThetaFiniteEnergyEmbedding F‖ := by
  change ‖cubicThetaFiniteEnergyEmbedding (cubicThetaInversionFinite F)‖≤_
  rw [cubicThetaInversionFinite_embedding_norm,one_mul]

lemma cubicThetaInversionFiniteExtension_finite (F : cubicThetaFiniteEnergySections) :
    cubicThetaInversionFiniteExtension (cubicThetaFiniteEnergyEmbedding F)=
      cubicThetaInversionRawEnergy F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaInversionRawEnergy) (e:=cubicThetaFiniteEnergyEmbedding)
    cubicThetaFiniteEnergyEmbedding_dense ⟨1,cubicThetaInversionRawEnergy_bound⟩ F

lemma cubicThetaInversionFiniteExtension_eq (u : cubicThetaGlobalEnergySpace) :
    cubicThetaInversionFiniteExtension u=cubicThetaInversionEnergy u := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq cubicThetaInversionFiniteExtension.continuous cubicThetaInversionEnergy.continuous) ?_
  intro F
  change cubicThetaInversionFiniteExtension (cubicThetaGlobalEnergyTest F)=_
  rw [←cubicThetaFiniteEnergyEmbedding_smooth,cubicThetaInversionFiniteExtension_finite]
  change cubicThetaInversionRawEnergy (cubicThetaSmoothToFiniteEnergy F)=
    cubicThetaInversionEnergy (cubicThetaGlobalEnergyTest F)
  rw [cubicThetaInversionEnergy_test]
  rfl

theorem cubicThetaInversionEnergy_finite (F : cubicThetaFiniteEnergySections) :
    cubicThetaInversionEnergy (cubicThetaFiniteEnergyEmbedding F)=
      cubicThetaFiniteEnergyEmbedding (cubicThetaInversionFinite F) := by
  rw [←cubicThetaInversionFiniteExtension_eq,cubicThetaInversionFiniteExtension_finite]
  rfl

end CubicFirstMoment

end

end OAI
