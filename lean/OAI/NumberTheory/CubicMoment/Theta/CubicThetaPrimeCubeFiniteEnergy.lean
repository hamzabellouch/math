import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeEnergyIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeEnergyDomainNorm

namespace OAI

/-! The literal cubed-prime Hecke operator preserves actual finite-energy
C1 sections. Both its value and gradient bounds are inherited from the
proved domain integral identities. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeFinite_mass_domain (F : cubicThetaFiniteEnergySections) :
    IntegrableOn (fun x => ‖F.val.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hn : Integrable (fun q => (cubicThetaSectionNorm F.val q)^2) cubicThetaQuotientMeasure := by
    simpa only [cubicThetaSectionRepresentative_norm] using
      F.property.2.1.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hc := hn.comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  simpa only [IntegrableOn,Function.comp_def,cubicThetaSectionNorm_apply] using hc

lemma cubicThetaPrimeCubeFinite_energy_domain (F : cubicThetaFiniteEnergySections) :
    IntegrableOn (cubicThetaSectionEnergy F.val) cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hn : Integrable (cubicThetaC1QuotientEnergy F.val) cubicThetaQuotientMeasure := by
    simpa only [cubicThetaC1Gradient_norm_sq F.val F.property.1] using
      F.property.2.2.integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hc := hn.comp_measurable cubicThetaQuotientMap_open.continuous.measurable
  simpa only [IntegrableOn,Function.comp_def,cubicThetaC1QuotientEnergy_apply F.val F.property.1] using hc

lemma cubicThetaPrimeCubeSection_memLp_of_domain (F : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure := by
  apply (memLp_two_iff_integrable_sq_norm (cubicThetaSectionRepresentative_measurable F).aestronglyMeasurable).mpr
  simp only [cubicThetaSectionRepresentative_norm]
  apply (integrable_map_measure ((cubicThetaSectionNorm_continuous F).pow 2).aestronglyMeasurable
    cubicThetaQuotientMap_open.continuous.measurable.aemeasurable).mpr
  simpa only [IntegrableOn,Function.comp_def,Pi.pow_apply,cubicThetaSectionNorm_apply] using hF

lemma cubicThetaPrimeCubeGradient_memLp_of_domain (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hE : IntegrableOn (cubicThetaSectionEnergy F) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    MemLp (cubicThetaGradientRepresentative F) 2 cubicThetaQuotientMeasure := by
  have hm : Measurable (cubicThetaGradientRepresentative F) :=
    (cubicThetaC1Gradient_continuous F hF).measurable.comp cubicThetaBorelSection_measurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  simp only [cubicThetaC1Gradient_norm_sq F hF]
  apply (integrable_map_measure (cubicThetaC1QuotientEnergy_continuous F hF).aestronglyMeasurable
    cubicThetaQuotientMap_open.continuous.measurable.aemeasurable).mpr
  simpa only [IntegrableOn,Function.comp_def,cubicThetaC1QuotientEnergy_apply F hF] using hE

def cubicThetaPrimeCubeHeckeFinite {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) : cubicThetaFiniteEnergySections :=
  ⟨cubicThetaPrimeCubeHecke hp F.val,cubicThetaPrimeCubeHecke_c1 hp F.val F.property.1,
    cubicThetaPrimeCubeSection_memLp_of_domain _
      (cubicThetaPrimeCubeTrace_integrable hp (cubicThetaPrimeCubeDilationSection hp F.val)
        (cubicThetaPrimeCubeDilation_integrable hp F.val (cubicThetaPrimeCubeFinite_mass_domain F))),
    cubicThetaPrimeCubeGradient_memLp_of_domain _ (cubicThetaPrimeCubeHecke_c1 hp F.val F.property.1)
      (cubicThetaPrimeCubeHecke_energy_integrable hp F.val F.property.1
        (cubicThetaPrimeCubeFinite_energy_domain F))⟩

theorem cubicThetaPrimeCubeHeckeFinite_value_bound {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyValue (cubicThetaPrimeCubeHeckeFinite hp F)‖^2≤
      ((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*‖cubicThetaFiniteEnergyValue F‖^2 := by
  rw [cubicThetaFiniteEnergyValue_domain_norm_sq,cubicThetaFiniteEnergyValue_domain_norm_sq]
  exact cubicThetaPrimeCubeHecke_integral_bound hp F.val (cubicThetaPrimeCubeFinite_mass_domain F)

theorem cubicThetaPrimeCubeHeckeFinite_gradient_bound {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    ‖cubicThetaFiniteEnergyGradient (cubicThetaPrimeCubeHeckeFinite hp F)‖^2≤
      ((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*‖cubicThetaFiniteEnergyGradient F‖^2 := by
  rw [cubicThetaFiniteEnergyGradient_domain_norm_sq,cubicThetaFiniteEnergyGradient_domain_norm_sq]
  exact cubicThetaPrimeCubeHecke_energy_integral_le hp F.val F.property.1
    (cubicThetaPrimeCubeFinite_energy_domain F)

end CubicFirstMoment

end

end OAI
