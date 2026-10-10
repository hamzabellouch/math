import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionL2Bounds

namespace OAI

/-! Exact degree scaling for restriction of an original automorphic
section to the finite prime cover. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaPrimeSectionRestrict_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    MemLp (cubicThetaPrimeSectionRepresentative hp (cubicThetaPrimeSectionRestrict hp F))
      2 (cubicThetaPrimeCoverMeasure hp) := by
  apply (memLp_norm_iff
    (cubicThetaPrimeSectionRepresentative_measurable hp _).aestronglyMeasurable).mp
  have hn := hF.norm
  simp only [cubicThetaSectionRepresentative_norm] at hn
  have hs := hn.smul_measure
    (by simp : ((cubicThetaPrimeCoverGroup hp).index : ℝ≥0∞)≠∞)
  rw [←cubicThetaPrimeCoverProjection_measure hp] at hs
  have hc := hs.comp_of_map (cubicThetaPrimeCoverProjection_continuous hp).measurable.aemeasurable
  simpa only [Function.comp_def,cubicThetaPrimeSectionRepresentative_norm,
    cubicThetaPrimeSectionRestrict_norm] using hc

theorem cubicThetaPrimeSectionRestrict_L2_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    ‖(cubicThetaPrimeSectionRestrict_memLp hp F hF).toLp
      (cubicThetaPrimeSectionRepresentative hp (cubicThetaPrimeSectionRestrict hp F))‖^2=
      ((cubicThetaPrimeCoverGroup hp).index:ℝ)*‖hF.toLp (cubicThetaSectionRepresentative F)‖^2 := by
  rw [cubicThetaPrimeSectionL2_norm_sq,cubicThetaSectionL2_norm_sq]
  simp_rw [cubicThetaPrimeSectionRestrict_norm]
  have hi := integral_map_of_stronglyMeasurable (μ:=cubicThetaPrimeCoverMeasure hp)
    (cubicThetaPrimeCoverProjection_continuous hp).measurable
    ((cubicThetaSectionNorm_continuous F).pow 2).stronglyMeasurable
  simp only [Pi.pow_apply] at hi
  rw [←hi,cubicThetaPrimeCoverProjection_measure hp,integral_smul_measure]
  simp only [ENNReal.toReal_natCast,smul_eq_mul]

end CubicFirstMoment

end

end OAI
