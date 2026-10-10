import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteEnergyPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeDerivativeAdjoint

namespace OAI

/-! The same literal inversion conjugate is the adjoint for the mass
and gradient forms on finite-energy sections. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeAdjointFinite {p : Eisenstein} (hp : primaryPrime p)
    (G : cubicThetaFiniteEnergySections) : cubicThetaFiniteEnergySections :=
  cubicThetaInversionFinite (cubicThetaPrimeCubeHeckeFinite hp (cubicThetaInversionFinite G))

lemma cubicThetaPrimeCubeHeckeFinite_mass_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaFiniteEnergyValue G)
      (cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeHeckeFinite hp F))=
    inner ℂ (cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeAdjointFinite hp G))
      (cubicThetaFiniteEnergyValue F) := by
  rw [cubicThetaFiniteEnergyValue_pairing,cubicThetaFiniteEnergyValue_pairing]
  change (∫ x in cubicThetaFundamentalDomain,
    inner ℂ (G.val.val x) ((cubicThetaPrimeCubeHecke hp F.val).val x) ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,inner ℂ
      ((cubicThetaInversionSection (cubicThetaPrimeCubeHecke hp (cubicThetaInversionSection G.val))).val x)
      (F.val.val x) ∂cubicThetaPointMeasure
  simpa only [RCLike.inner_apply',Complex.star_def] using
    cubicThetaPrimeCubeHecke_mass_adjoint hp F.val G.val
      (cubicThetaPrimeCubeFinite_mass_domain F) (cubicThetaPrimeCubeFinite_mass_domain G)

lemma cubicThetaPrimeCubeHeckeFinite_gradient_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaFiniteEnergyGradient G)
      (cubicThetaFiniteEnergyGradient (cubicThetaPrimeCubeHeckeFinite hp F))=
    inner ℂ (cubicThetaFiniteEnergyGradient (cubicThetaPrimeCubeAdjointFinite hp G))
      (cubicThetaFiniteEnergyGradient F) := by
  rw [cubicThetaFiniteEnergyGradient_pairing,cubicThetaFiniteEnergyGradient_pairing]
  exact cubicThetaPrimeCubeHecke_gradient_adjoint hp F G

end CubicFirstMoment

end

end OAI
