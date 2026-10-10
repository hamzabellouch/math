import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootRestrictionBound

namespace OAI

/-! The original automorphic L2 norm acquires exactly the finite-cover
degree under restriction to the root cover. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CubicFirstMoment

lemma cubicThetaPrimeRootSectionRestrict_memLp {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    MemLp (cubicThetaPrimeRootSectionRepresentative hp (cubicThetaPrimeRootSectionRestrict F))
      2 (cubicThetaPrimeRootCoverMeasure hp) := by
  apply (memLp_norm_iff
    (cubicThetaPrimeRootSectionRepresentative_measurable hp _).aestronglyMeasurable).mp
  have hn := hF.norm
  simp only [cubicThetaSectionRepresentative_norm] at hn
  have hs := hn.smul_measure
    (by simp : ((cubicThetaPrimeRootCoverGroup hp).index:ℝ≥0∞)≠∞)
  rw [←cubicThetaPrimeRootCoverProjection_measure hp] at hs
  have hc := hs.comp_of_map (cubicThetaPrimeRootCoverProjection_continuous hp).measurable.aemeasurable
  simpa only [Function.comp_def,cubicThetaPrimeRootSectionRepresentative_norm,
    cubicThetaPrimeRootSectionRestrict_norm] using hc

theorem cubicThetaPrimeRootSectionRestrict_L2_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure) :
    ‖(cubicThetaPrimeRootSectionRestrict_memLp hp F hF).toLp
      (cubicThetaPrimeRootSectionRepresentative hp (cubicThetaPrimeRootSectionRestrict F))‖^2=
      ((cubicThetaPrimeRootCoverGroup hp).index:ℝ)*‖hF.toLp (cubicThetaSectionRepresentative F)‖^2 := by
  rw [cubicThetaPrimeRootSectionL2_norm_sq,cubicThetaSectionL2_norm_sq]
  exact cubicThetaPrimeRootSectionRestrict_mass hp F

end CubicFirstMoment

end

end OAI
