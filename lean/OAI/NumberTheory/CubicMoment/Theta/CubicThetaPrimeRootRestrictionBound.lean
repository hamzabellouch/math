import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootCoverDegree
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootAverageBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionL2Bounds

namespace OAI

/-! Apply the root-average contraction to actual global sections. The
finite-cover degree supplies the exact normalization of their square norm. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaPrimeRootSectionRestrict_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (q : CubicThetaPrimeRootCover hp) :
    cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootSectionRestrict F) q=
      cubicThetaSectionNorm F (cubicThetaPrimeRootCoverProjection hp q) := by
  induction q using Quotient.inductionOn with
  | h y => exact (cubicThetaSectionNorm_apply F y).symm

lemma cubicThetaPrimeRootSectionRestrict_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : Integrable (fun q => (cubicThetaSectionNorm F q)^2) cubicThetaQuotientMeasure) :
    Integrable (fun q => (cubicThetaPrimeRootSectionNorm hp
      (cubicThetaPrimeRootSectionRestrict F) q)^2) (cubicThetaPrimeRootCoverMeasure hp) := by
  have hs := hF.smul_measure (by simp : ((cubicThetaPrimeRootCoverGroup hp).index:ℝ≥0∞)≠∞)
  rw [←cubicThetaPrimeRootCoverProjection_measure hp] at hs
  have hc := hs.comp_measurable (cubicThetaPrimeRootCoverProjection_continuous hp).measurable
  simpa only [Function.comp_def,cubicThetaPrimeRootSectionRestrict_norm] using hc

theorem cubicThetaPrimeRootSectionRestrict_mass {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) :
    (∫ q, (cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootSectionRestrict F) q)^2
      ∂cubicThetaPrimeRootCoverMeasure hp)=
      ((cubicThetaPrimeRootCoverGroup hp).index:ℝ)*
        ∫ q, (cubicThetaSectionNorm F q)^2 ∂cubicThetaQuotientMeasure := by
  simp_rw [cubicThetaPrimeRootSectionRestrict_norm]
  have hi := integral_map_of_stronglyMeasurable (μ:=cubicThetaPrimeRootCoverMeasure hp)
    (cubicThetaPrimeRootCoverProjection_continuous hp).measurable
    ((cubicThetaSectionNorm_continuous F).pow 2).stronglyMeasurable
  simp only [Pi.pow_apply] at hi
  rw [←hi,cubicThetaPrimeRootCoverProjection_measure hp,integral_smul_measure]
  simp only [ENNReal.toReal_natCast,smul_eq_mul]

theorem cubicThetaPrimeRootRestriction_average_mass_le {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : Integrable (fun q => (cubicThetaSectionNorm F q)^2) cubicThetaQuotientMeasure) :
    (∫ q, (cubicThetaPrimeRootSectionNorm hp
      (cubicThetaPrimeRootAverage hp (cubicThetaPrimeRootSectionRestrict F)) q)^2
      ∂cubicThetaPrimeRootCoverMeasure hp)≤
      ((cubicThetaPrimeRootCoverGroup hp).index:ℝ)*
        ∫ q, (cubicThetaSectionNorm F q)^2 ∂cubicThetaQuotientMeasure := by
  rw [←cubicThetaPrimeRootSectionRestrict_mass hp F]
  exact cubicThetaPrimeRootAverage_mass_le hp _ (cubicThetaPrimeRootSectionRestrict_integrable hp F hF)

end CubicFirstMoment

end

end OAI
