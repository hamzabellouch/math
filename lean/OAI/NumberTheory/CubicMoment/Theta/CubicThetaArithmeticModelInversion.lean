import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBorelInversion
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBaseScalarNonzero
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueInversion

namespace OAI

/-! The inversion symmetry of the actual residual vector holds
pointwise for its continuous arithmetic Fourier expansion. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaBorelInversion_smooth (F : cubicThetaSmoothTests) :
    cubicThetaBorelInversion (cubicThetaGlobalMass F)=
      cubicThetaGlobalMass (cubicThetaInversionSmooth F) := by
  apply Lp.ext
  have hcomp := (cubicThetaIntegralQuotient_measurePreserving
    cubicThetaFullInversion).quasiMeasurePreserving.ae
      (cubicThetaSectionRepresentative_memLp F).coeFn_toLp
  filter_upwards [(cubicThetaBorelInversionFunction_memLp
    (cubicThetaGlobalMass F)).coeFn_toLp,
    (cubicThetaSectionRepresentative_memLp (cubicThetaInversionSmooth F)).coeFn_toLp,
    hcomp] with q hT hI hF
  change ((cubicThetaBorelInversionFunction_memLp (cubicThetaGlobalMass F)).toLp _) q=
    ((cubicThetaSectionRepresentative_memLp (cubicThetaInversionSmooth F)).toLp _) q
  rw [hT,hI]
  unfold cubicThetaBorelInversionFunction
  change cubicThetaBorelPhase (cubicThetaFullInversion • cubicThetaBorelSection q)*
    (cubicThetaGlobalMass F) (cubicThetaQuotientMap
      (cubicThetaFullInversion • cubicThetaBorelSection q))=
        F.val.val (cubicThetaFullInversion • cubicThetaBorelSection q)
  have he : (cubicThetaGlobalMass F) (cubicThetaQuotientMap
      (cubicThetaFullInversion • cubicThetaBorelSection q))=
      cubicThetaSectionRepresentative F (cubicThetaQuotientMap
        (cubicThetaFullInversion • cubicThetaBorelSection q)) := by
    change (cubicThetaGlobalMass F) (cubicThetaIntegralQuotientMap cubicThetaFullInversion q)=
      cubicThetaSectionRepresentative F (cubicThetaIntegralQuotientMap cubicThetaFullInversion q) at hF
    simpa only [←cubicThetaIntegralQuotientMap_apply,cubicThetaBorelSection_rightInverse q]
      using hF
  rw [he]
  exact cubicThetaBorelLift_section F (cubicThetaFullInversion • cubicThetaBorelSection q)

theorem cubicThetaBorelInversion_energy (u : cubicThetaGlobalEnergySpace) :
    cubicThetaBorelInversion (cubicThetaGlobalInclusion u)=
      cubicThetaGlobalInclusion (cubicThetaInversionEnergy u) := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq (cubicThetaBorelInversion.continuous.comp cubicThetaGlobalInclusion.continuous)
      (cubicThetaGlobalInclusion.continuous.comp cubicThetaInversionEnergy.continuous)) ?_
  intro F
  change cubicThetaBorelInversion (cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F))=
    cubicThetaGlobalInclusion (cubicThetaInversionEnergy (cubicThetaGlobalEnergyTest F))
  rw [cubicThetaInversionEnergy_test,cubicThetaGlobalInclusion_test,
    cubicThetaGlobalInclusion_test,cubicThetaBorelInversion_smooth]

theorem cubicThetaNormalizedArithmeticResidue_inversion :
    cubicThetaInversionEnergy cubicThetaNormalizedArithmeticResidue=
      cubicThetaNormalizedArithmeticResidue := by
  unfold cubicThetaNormalizedArithmeticResidue
  rw [map_smul,cubicThetaArithmeticResidueEnergy_inversion]

theorem cubicThetaArithmeticModel_inversion (p : CubicThetaPoint) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (cubicThetaFullInversion • p).val=
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val := by
  have hT := cubicThetaBorelInversion_lift
    (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)
  rw [cubicThetaBorelInversion_energy,cubicThetaNormalizedArithmeticResidue_inversion] at hT
  have hcomp := (measurePreserving_smul cubicThetaFullInversion
    cubicThetaPointMeasure).quasiMeasurePreserving.ae cubicThetaArithmeticModel_global_ae
  have he : (fun p : CubicThetaPoint => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaFullInversion • p).val)=ᵐ[cubicThetaPointMeasure]
        (fun p => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val) := by
    filter_upwards [cubicThetaArithmeticModel_global_ae,hcomp,hT] with q hq hSq hIq
    exact hSq.symm.trans (hIq.symm.trans hq)
  have hc := cubicThetaArithmeticModel_point_continuous cubicThetaArithmeticBaseScalar
  exact congrFun (Measure.eq_of_ae_eq he
    (hc.comp (continuous_const_smul cubicThetaFullInversion)) hc) p

end CubicFirstMoment

end

end OAI
