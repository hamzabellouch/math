import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionEnergyInvolution
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionPairing

namespace OAI

/-! Transport of actual section pairings under inversion. Only the
test section is inverted in the energy-space application. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaInversionSection_memLp (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    MemLp (cubicThetaSectionRepresentative (cubicThetaInversionSection F)) 2
      cubicThetaQuotientMeasure := by
  have hn : MemLp (cubicThetaSectionNorm F) 2 cubicThetaQuotientMeasure := by
    simpa only [cubicThetaSectionRepresentative_norm] using hF.norm
  have hi := hn.comp_measurePreserving
    (cubicThetaIntegralQuotient_measurePreserving cubicThetaFullInversion)
  apply (memLp_norm_iff
    (cubicThetaSectionRepresentative_measurable (cubicThetaInversionSection F)).aestronglyMeasurable).mp
  simpa only [Function.comp_def,cubicThetaSectionRepresentative_norm,
    cubicThetaInversionSection_norm] using hi

lemma cubicThetaInversion_pairing (F G : CubicThetaSection) (q : CubicThetaQuotient) :
    cubicThetaSectionPairing (cubicThetaInversionSection F) G q=
      cubicThetaSectionPairing F (cubicThetaInversionSection G)
        (cubicThetaIntegralQuotientMap cubicThetaFullInversion q) := by
  obtain ⟨p,rfl⟩ := cubicThetaQuotientMap_surjective q
  rw [cubicThetaIntegralQuotientMap_apply,cubicThetaSectionPairing_apply,
    cubicThetaSectionPairing_apply]
  change inner ℂ (F.val (cubicThetaFullInversion • p)) (G.val p)=
    inner ℂ (F.val (cubicThetaFullInversion • p))
      (G.val (cubicThetaFullInversion • (cubicThetaFullInversion • p)))
  rw [cubicThetaFullInversion_involutive]

lemma cubicThetaInversion_pairing_integral (F G : CubicThetaSection) :
    (∫ q, cubicThetaSectionPairing (cubicThetaInversionSection F) G q
      ∂cubicThetaQuotientMeasure)=
    ∫ q, cubicThetaSectionPairing F (cubicThetaInversionSection G) q
      ∂cubicThetaQuotientMeasure := by
  simp_rw [cubicThetaInversion_pairing]
  exact (cubicThetaIntegralQuotient_measurePreserving cubicThetaFullInversion).integral_comp
    (cubicThetaIntegralQuotientHomeomorph cubicThetaFullInversion).measurableEmbedding
    (cubicThetaSectionPairing F (cubicThetaInversionSection G))

lemma cubicThetaInversionEnergy_mass_flip (u v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalInclusion (cubicThetaInversionEnergy u))
      (cubicThetaGlobalInclusion v)=
    inner ℂ (cubicThetaGlobalInclusion u)
      (cubicThetaGlobalInclusion (cubicThetaInversionEnergy v)) := by
  have h := cubicThetaInversionEnergy_mass_inner u (cubicThetaInversionEnergy v)
  rw [cubicThetaInversionEnergy_involutive] at h
  exact h

end CubicFirstMoment

end

end OAI
