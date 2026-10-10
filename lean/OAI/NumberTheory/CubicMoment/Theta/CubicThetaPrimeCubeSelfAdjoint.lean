import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSelfAdjointSection

namespace OAI

/-! The actual mass, gradient, and completed energy pairings are symmetric
for the cubed-prime correspondence. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeAdjointFinite_eq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    cubicThetaPrimeCubeAdjointFinite hp F=cubicThetaPrimeCubeHeckeFinite hp F := by
  apply Subtype.ext
  exact cubicThetaPrimeCubeHecke_inversion_adjoint hp F.val

theorem cubicThetaPrimeCubeHeckeAdjoint_eq {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeHeckeAdjoint hp=cubicThetaPrimeCubeHeckeEnergy hp := by
  apply ContinuousLinearMap.ext
  intro u
  refine cubicThetaFiniteEnergyEmbedding_dense.induction_on u
    (isClosed_eq (cubicThetaPrimeCubeHeckeAdjoint hp).continuous
      (cubicThetaPrimeCubeHeckeEnergy hp).continuous) ?_
  intro F
  rw [cubicThetaPrimeCubeHeckeAdjoint_finite,cubicThetaPrimeCubeHeckeEnergy_finite,
    cubicThetaPrimeCubeAdjointFinite_eq]
  rfl

theorem cubicThetaPrimeCubeHecke_mass_symmetric {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalInclusion u) (cubicThetaGlobalInclusion (cubicThetaPrimeCubeHeckeEnergy hp v))=
      inner ℂ (cubicThetaGlobalInclusion (cubicThetaPrimeCubeHeckeEnergy hp u)) (cubicThetaGlobalInclusion v) := by
  rw [cubicThetaPrimeCubeHeckeEnergy_mass_adjoint,cubicThetaPrimeCubeHeckeAdjoint_eq]

theorem cubicThetaPrimeCubeHecke_gradient_symmetric {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient u) (cubicThetaGlobalEnergyGradient (cubicThetaPrimeCubeHeckeEnergy hp v))=
      inner ℂ (cubicThetaGlobalEnergyGradient (cubicThetaPrimeCubeHeckeEnergy hp u)) (cubicThetaGlobalEnergyGradient v) := by
  rw [cubicThetaPrimeCubeHeckeEnergy_gradient_adjoint,cubicThetaPrimeCubeHeckeAdjoint_eq]

theorem cubicThetaPrimeCubeHecke_symmetric {p : Eisenstein} (hp : primaryPrime p)
    (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ u (cubicThetaPrimeCubeHeckeEnergy hp v)=inner ℂ (cubicThetaPrimeCubeHeckeEnergy hp u) v := by
  rw [cubicThetaPrimeCubeHeckeEnergy_adjoint,cubicThetaPrimeCubeHeckeAdjoint_eq]

end CubicFirstMoment

end

end OAI
