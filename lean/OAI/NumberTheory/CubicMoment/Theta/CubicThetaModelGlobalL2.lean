import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticModelSection

namespace OAI

/-! The continuous arithmetic model is the actual global L2 residue,
not only its restriction to a cusp. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaArithmeticModelRepresentative_ae :
    cubicThetaSectionRepresentative cubicThetaArithmeticModelSection
      =ᵐ[cubicThetaQuotientMeasure]
        (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue :
          CubicThetaQuotient → ℂ) := by
  let R := cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue
  have hp : ∀ᵐ p ∂cubicThetaPointMeasure,
      cubicThetaSectionRepresentative cubicThetaArithmeticModelSection (cubicThetaQuotientMap p)=
        R (cubicThetaQuotientMap p) := by
    filter_upwards [cubicThetaArithmeticModel_global_ae] with p hp
    have he := cubicThetaBorelLift_section cubicThetaArithmeticModelSection p
    have hh : cubicThetaBorelPhase p*
        cubicThetaSectionRepresentative cubicThetaArithmeticModelSection (cubicThetaQuotientMap p)=
        cubicThetaBorelPhase p*R (cubicThetaQuotientMap p) := he.trans hp.symm
    exact mul_left_cancel₀ (norm_ne_zero_iff.mp (by rw [cubicThetaBorelPhase_norm]; norm_num)) hh
  change ∀ᵐ q ∂cubicThetaQuotientMeasure,
    cubicThetaSectionRepresentative cubicThetaArithmeticModelSection q=R q
  change ∀ᵐ q ∂(cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain).map
    cubicThetaQuotientMap, cubicThetaSectionRepresentative cubicThetaArithmeticModelSection q=R q
  apply (ae_map_iff cubicThetaQuotientMap_open.continuous.measurable.aemeasurable
    (measurableSet_eq_fun (cubicThetaSectionRepresentative_measurable _)
      (Lp.stronglyMeasurable R).measurable)).mpr
  exact ae_mono Measure.restrict_le_self hp

lemma cubicThetaArithmeticModelGlobal_memLp :
    MemLp (cubicThetaSectionRepresentative cubicThetaArithmeticModelSection)
      2 cubicThetaQuotientMeasure :=
  (memLp_congr_ae cubicThetaArithmeticModelRepresentative_ae).mpr
    (Lp.memLp (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue))

theorem cubicThetaArithmeticModelGlobalL2 :
    cubicThetaArithmeticModelGlobal_memLp.toLp
        (cubicThetaSectionRepresentative cubicThetaArithmeticModelSection)=
      cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue := by
  apply Lp.ext
  exact cubicThetaArithmeticModelGlobal_memLp.coeFn_toLp.trans
    cubicThetaArithmeticModelRepresentative_ae

end CubicFirstMoment

end

end OAI
