import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionFiniteCompletion

namespace OAI

/-! Literal domain formulas for both Hermitian pairings on actual
finite-energy sections. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaFiniteEnergyValue_pairing (F G : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaFiniteEnergyValue F) (cubicThetaFiniteEnergyValue G)=
      ∫ x in cubicThetaFundamentalDomain,inner ℂ (F.val.val x) (G.val.val x) ∂cubicThetaPointMeasure := by
  change inner ℂ (F.property.2.1.toLp _) (G.property.2.1.toLp _)=_
  rw [cubicThetaSectionPairing_L2 F.val G.val F.property.2.1 G.property.2.1,cubicThetaQuotientMeasure]
  have he := integral_map_of_stronglyMeasurable
    (μ:=cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain)
    cubicThetaQuotientMap_open.continuous.measurable
    (cubicThetaSectionPairing_continuous F.val G.val).stronglyMeasurable
  simpa only [cubicThetaSectionPairing_apply] using he

lemma cubicThetaFiniteEnergyGradient_pairing (F G : cubicThetaFiniteEnergySections) :
    inner ℂ (cubicThetaFiniteEnergyGradient F) (cubicThetaFiniteEnergyGradient G)=
      ∫ x in cubicThetaFundamentalDomain,
        inner ℂ (cubicThetaSectionGradient F.val x) (cubicThetaSectionGradient G.val x)
          ∂cubicThetaPointMeasure := by
  change inner ℂ (F.property.2.2.toLp _) (G.property.2.2.toLp _)=_
  rw [cubicThetaC1Pairing_L2 F.val G.val F.property.1 G.property.1 F.property.2.2 G.property.2.2,
    cubicThetaQuotientMeasure]
  have he := integral_map_of_stronglyMeasurable
    (μ:=cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain)
    cubicThetaQuotientMap_open.continuous.measurable
    (cubicThetaC1Pairing_continuous F.val G.val F.property.1 G.property.1).stronglyMeasurable
  simpa only [cubicThetaC1Pairing_apply F.val G.val F.property.1 G.property.1] using he

end CubicFirstMoment

end

end OAI
