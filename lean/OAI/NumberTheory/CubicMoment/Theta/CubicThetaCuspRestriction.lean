import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteCuspRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalLocalRellich

namespace OAI

/-! Bounded restriction from the completed global energy space to the
literal high cusp strip, extending all actual C1 finite-energy sections. -/
noncomputable section
namespace CubicFirstMoment

local instance finiteEnergy_addCommGroup : AddCommGroup cubicThetaFiniteEnergySections :=
  Module.addCommMonoidToAddCommGroup ℂ

lemma cubicThetaFiniteEnergyEmbedding_dense : DenseRange cubicThetaFiniteEnergyEmbedding := by
  have h : DenseRange (fun F : cubicThetaSmoothTests =>
      cubicThetaFiniteEnergyEmbedding (cubicThetaSmoothToFiniteEnergy F)) := by
    have he : (fun F : cubicThetaSmoothTests =>
        cubicThetaFiniteEnergyEmbedding (cubicThetaSmoothToFiniteEnergy F))=
        (fun F => cubicThetaGlobalEnergyTestLinear F) := by
      funext F
      exact cubicThetaFiniteEnergyEmbedding_smooth F
    rw [he]
    exact cubicThetaGlobalEnergyTestLinear_dense
  exact h.of_comp

lemma cubicThetaFiniteCuspRestriction_energy_bound :
    ∃ C, ∀ F : cubicThetaFiniteEnergySections,
      ‖cubicThetaFiniteCuspRestriction F‖≤C*‖cubicThetaFiniteEnergyEmbedding F‖ := by
  refine ⟨1,fun F => ?_⟩
  simpa only [one_mul] using (cubicThetaFiniteCuspRestriction_bound F).trans
    (cubicThetaGlobalInclusion_bound (cubicThetaFiniteEnergyEmbedding F))

def cubicThetaCuspRestriction : cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaStripL2 :=
  LinearMap.extendOfNorm (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (E:=cubicThetaFiniteEnergySections) (Eₗ:=cubicThetaGlobalEnergySpace) (F:=CubicThetaStripL2)
    cubicThetaFiniteCuspRestriction cubicThetaFiniteEnergyEmbedding

lemma cubicThetaCuspRestriction_finiteEnergy (F : cubicThetaFiniteEnergySections) :
    cubicThetaCuspRestriction (cubicThetaFiniteEnergyEmbedding F)=cubicThetaFiniteCuspRestriction F :=
  LinearMap.extendOfNorm_eq (𝕜:=ℂ) (𝕜₂:=ℂ) (σ₁₂:=RingHom.id ℂ)
    (f:=cubicThetaFiniteCuspRestriction) (e:=cubicThetaFiniteEnergyEmbedding)
    cubicThetaFiniteEnergyEmbedding_dense cubicThetaFiniteCuspRestriction_energy_bound F

lemma cubicThetaCuspRestriction_norm : ‖cubicThetaCuspRestriction‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  have hc : IsClosed {v : cubicThetaGlobalEnergySpace | ‖cubicThetaCuspRestriction v‖≤1*‖v‖} :=
    isClosed_le cubicThetaCuspRestriction.continuous.norm (continuous_const.mul continuous_norm)
  have hr : Set.range cubicThetaFiniteEnergyEmbedding⊆
      {v : cubicThetaGlobalEnergySpace | ‖cubicThetaCuspRestriction v‖≤1*‖v‖} := by
    rintro _ ⟨F,rfl⟩
    change ‖cubicThetaCuspRestriction (cubicThetaFiniteEnergyEmbedding F)‖≤
      1*‖cubicThetaFiniteEnergyEmbedding F‖
    rw [cubicThetaCuspRestriction_finiteEnergy]
    simpa only [one_mul] using (cubicThetaFiniteCuspRestriction_bound F).trans
      (cubicThetaGlobalInclusion_bound (cubicThetaFiniteEnergyEmbedding F))
  exact (closure_minimal hr hc) (cubicThetaFiniteEnergyEmbedding_dense u)

end CubicFirstMoment

end

end OAI
