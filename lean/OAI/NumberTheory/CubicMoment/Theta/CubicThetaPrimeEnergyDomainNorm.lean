import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeEnergySpace
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteEnergySections

namespace OAI

/-! Literal fundamental-domain formulas for the two coordinates of
the original and prime-cover energy graphs. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeEnergyValue_domain_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    ‖cubicThetaPrimeEnergyValue hp F‖^2=
        ∫ x in cubicThetaPrimeCoverDomain hp, ‖F.val.val.val x‖^2 ∂cubicThetaPointMeasure := by
  change ‖F.property.1.toLp (cubicThetaPrimeSectionRepresentative hp F.val.val)‖^2=_
  rw [cubicThetaPrimeSectionL2_norm_sq]
  exact integral_map_of_stronglyMeasurable
    (cubicThetaPrimeCoverMap_open hp).continuous.measurable
    ((cubicThetaPrimeSectionNorm_continuous hp F.val.val).pow 2).stronglyMeasurable

lemma cubicThetaPrimeEnergyGradient_domain_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeFiniteEnergy hp) :
    ‖cubicThetaPrimeEnergyGradient hp F‖^2=
      ∫ x in cubicThetaPrimeCoverDomain hp, cubicThetaPrimeSectionEnergy hp F.val.val x
        ∂cubicThetaPointMeasure := by
  rw [cubicThetaPrimeEnergyGradient_norm_sq]
  exact integral_map_of_stronglyMeasurable
    (cubicThetaPrimeCoverMap_open hp).continuous.measurable
    (cubicThetaPrimeQuotientEnergy_continuous hp F.val).stronglyMeasurable

lemma cubicThetaFiniteEnergyValue_domain_norm_sq (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyValue F‖^2=
      ∫ x in cubicThetaFundamentalDomain, ‖F.val.val x‖^2 ∂cubicThetaPointMeasure := by
  change ‖F.property.2.1.toLp (cubicThetaSectionRepresentative F.val)‖^2=_
  rw [cubicThetaSectionL2_norm_sq,cubicThetaQuotientMeasure]
  have hi := integral_map_of_stronglyMeasurable
    (μ:=cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain)
    cubicThetaQuotientMap_open.continuous.measurable
    ((cubicThetaSectionNorm_continuous F.val).pow 2).stronglyMeasurable
  simpa only [Pi.pow_apply,cubicThetaSectionNorm_apply] using hi

lemma cubicThetaFiniteEnergyGradient_domain_norm_sq (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyGradient F‖^2=
      ∫ x in cubicThetaFundamentalDomain, cubicThetaSectionEnergy F.val x
        ∂cubicThetaPointMeasure := by
  have he : ‖cubicThetaFiniteEnergyGradient F‖^2=
      ∫ q, cubicThetaC1QuotientEnergy F.val q ∂cubicThetaQuotientMeasure := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [F.property.2.2.coeFn_toLp] with q hq
    change ‖(F.property.2.2.toLp _) q‖^2=_
    rw [hq,cubicThetaC1Gradient_norm_sq F.val F.property.1]
  rw [he,cubicThetaQuotientMeasure]
  have hi := integral_map_of_stronglyMeasurable
    (μ:=cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain)
    cubicThetaQuotientMap_open.continuous.measurable
    (cubicThetaC1QuotientEnergy_continuous F.val F.property.1).stronglyMeasurable
  simpa only [cubicThetaC1QuotientEnergy_apply F.val F.property.1] using hi

end CubicFirstMoment

end

end OAI
