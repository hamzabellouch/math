import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionL2Bounds

namespace OAI

/-! The literal inverted cusp restriction extends continuously from
finite-energy sections and agrees with inversion on the energy completion. -/
noncomputable section
namespace CubicFirstMoment
local instance : AddCommGroup cubicThetaFiniteEnergySections := Module.addCommMonoidToAddCommGroup ℂ

lemma cubicThetaInvertedFiniteRestriction_energy_bound :
    ∃ C, ∀ F : cubicThetaFiniteEnergySections,
      ‖cubicThetaInvertedFiniteRestriction F‖≤C*‖cubicThetaFiniteEnergyEmbedding F‖ := by
  refine ⟨1,fun F => ?_⟩
  simpa only [one_mul] using (cubicThetaInvertedFiniteRestriction_bound F).trans
    (cubicThetaGlobalInclusion_bound (cubicThetaFiniteEnergyEmbedding F))

def cubicThetaInvertedFiniteExtension : cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaStripL2 :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (E:=cubicThetaFiniteEnergySections) (Eₗ:=cubicThetaGlobalEnergySpace) (F:=CubicThetaStripL2)
    cubicThetaInvertedFiniteRestriction cubicThetaFiniteEnergyEmbedding

lemma cubicThetaInvertedFiniteExtension_finite (F : cubicThetaFiniteEnergySections) :
    cubicThetaInvertedFiniteExtension (cubicThetaFiniteEnergyEmbedding F)=
      cubicThetaInvertedFiniteRestriction F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaInvertedFiniteRestriction) (e:=cubicThetaFiniteEnergyEmbedding)
    cubicThetaFiniteEnergyEmbedding_dense cubicThetaInvertedFiniteRestriction_energy_bound F

lemma cubicThetaInvertedFiniteExtension_test (F : cubicThetaSmoothTests) :
    cubicThetaInvertedFiniteExtension (cubicThetaGlobalEnergyTest F)=
      cubicThetaCuspRestriction (cubicThetaInversionEnergy (cubicThetaGlobalEnergyTest F)) := by
  calc
    _ = cubicThetaInvertedFiniteRestriction (cubicThetaSmoothToFiniteEnergy F) := by
      rw [←cubicThetaFiniteEnergyEmbedding_smooth,cubicThetaInvertedFiniteExtension_finite]
    _ = _ := by
      rw [cubicThetaInversionEnergy_test,
        ←cubicThetaFiniteEnergyEmbedding_smooth,cubicThetaCuspRestriction_finiteEnergy]
      rfl

theorem cubicThetaInvertedFiniteExtension_eq (u : cubicThetaGlobalEnergySpace) :
    cubicThetaInvertedFiniteExtension u=
      cubicThetaCuspRestriction (cubicThetaInversionEnergy u) := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq cubicThetaInvertedFiniteExtension.continuous
      (cubicThetaCuspRestriction.continuous.comp cubicThetaInversionEnergy.continuous)) ?_
  exact cubicThetaInvertedFiniteExtension_test

theorem cubicThetaCuspRestriction_inversion_finite (F : cubicThetaFiniteEnergySections) :
    cubicThetaCuspRestriction (cubicThetaInversionEnergy (cubicThetaFiniteEnergyEmbedding F))=
      cubicThetaInvertedFiniteRestriction F :=
  (cubicThetaInvertedFiniteExtension_eq _).symm.trans (cubicThetaInvertedFiniteExtension_finite F)

end CubicFirstMoment

end

end OAI
