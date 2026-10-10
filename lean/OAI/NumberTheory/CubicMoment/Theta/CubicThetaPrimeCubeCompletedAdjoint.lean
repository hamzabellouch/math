import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFiniteAdjoint

namespace OAI

/-! Both finite pairings extend to the completed global energy
space. The adjoint is the actual inversion-conjugated correspondence. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeHeckeAdjoint {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace :=
  cubicThetaInversionEnergy.toContinuousLinearMap.comp
    ((cubicThetaPrimeCubeHeckeEnergy hp).comp cubicThetaInversionEnergy.toContinuousLinearMap)

lemma cubicThetaPrimeCubeHeckeAdjoint_finite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    cubicThetaPrimeCubeHeckeAdjoint hp (cubicThetaFiniteEnergyEmbedding F)=
      cubicThetaFiniteEnergyEmbedding (cubicThetaPrimeCubeAdjointFinite hp F) := by
  change cubicThetaInversionEnergy (cubicThetaPrimeCubeHeckeEnergy hp
    (cubicThetaInversionEnergy (cubicThetaFiniteEnergyEmbedding F)))=_
  rw [cubicThetaInversionEnergy_finite,cubicThetaPrimeCubeHeckeEnergy_finite]
  change cubicThetaInversionEnergy (cubicThetaFiniteEnergyEmbedding
    (cubicThetaPrimeCubeHeckeFinite hp (cubicThetaInversionFinite F)))=_
  exact cubicThetaInversionEnergy_finite _

theorem cubicThetaPrimeCubeHeckeEnergy_mass_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalInclusion u) (cubicThetaGlobalInclusion (cubicThetaPrimeCubeHeckeEnergy hp v))=
      inner ℂ (cubicThetaGlobalInclusion (cubicThetaPrimeCubeHeckeAdjoint hp u)) (cubicThetaGlobalInclusion v) := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq (cubicThetaGlobalInclusion.continuous.inner continuous_const)
      ((cubicThetaGlobalInclusion.continuous.comp (cubicThetaPrimeCubeHeckeAdjoint hp).continuous).inner
        continuous_const)) ?_
  intro F
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on v
    (isClosed_eq (continuous_const.inner (cubicThetaGlobalInclusion.continuous.comp
      (cubicThetaPrimeCubeHeckeEnergy hp).continuous))
      (continuous_const.inner cubicThetaGlobalInclusion.continuous)) ?_
  intro G
  rw [cubicThetaPrimeCubeHeckeEnergy_finite,cubicThetaPrimeCubeHeckeAdjoint_finite]
  change inner ℂ (cubicThetaFiniteEnergyValue F)
      (cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeHeckeFinite hp G))=
    inner ℂ (cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeAdjointFinite hp F))
      (cubicThetaFiniteEnergyValue G)
  exact cubicThetaPrimeCubeHeckeFinite_mass_adjoint hp G F

theorem cubicThetaPrimeCubeHeckeEnergy_gradient_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient u)
      (cubicThetaGlobalEnergyGradient (cubicThetaPrimeCubeHeckeEnergy hp v))=
    inner ℂ (cubicThetaGlobalEnergyGradient (cubicThetaPrimeCubeHeckeAdjoint hp u))
      (cubicThetaGlobalEnergyGradient v) := by
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq (cubicThetaGlobalEnergyGradient.continuous.inner continuous_const)
      ((cubicThetaGlobalEnergyGradient.continuous.comp (cubicThetaPrimeCubeHeckeAdjoint hp).continuous).inner
        continuous_const)) ?_
  intro F
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on v
    (isClosed_eq (continuous_const.inner (cubicThetaGlobalEnergyGradient.continuous.comp
      (cubicThetaPrimeCubeHeckeEnergy hp).continuous))
      (continuous_const.inner cubicThetaGlobalEnergyGradient.continuous)) ?_
  intro G
  rw [cubicThetaPrimeCubeHeckeEnergy_finite,cubicThetaPrimeCubeHeckeAdjoint_finite]
  change inner ℂ (cubicThetaFiniteEnergyGradient F)
      (cubicThetaFiniteEnergyGradient (cubicThetaPrimeCubeHeckeFinite hp G))=
    inner ℂ (cubicThetaFiniteEnergyGradient (cubicThetaPrimeCubeAdjointFinite hp F))
      (cubicThetaFiniteEnergyGradient G)
  exact cubicThetaPrimeCubeHeckeFinite_gradient_adjoint hp G F

theorem cubicThetaPrimeCubeHeckeEnergy_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ u (cubicThetaPrimeCubeHeckeEnergy hp v)=inner ℂ (cubicThetaPrimeCubeHeckeAdjoint hp u) v := by
  rw [cubicThetaGlobalEnergy_inner,cubicThetaGlobalEnergy_inner,
    cubicThetaPrimeCubeHeckeEnergy_mass_adjoint,cubicThetaPrimeCubeHeckeEnergy_gradient_adjoint]

end CubicFirstMoment

end

end OAI
