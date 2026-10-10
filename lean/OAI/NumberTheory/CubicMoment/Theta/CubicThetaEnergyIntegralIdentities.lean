import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreRestriction
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspScalarIntegrals

namespace OAI

/-! The completed energy coordinates and compact restrictions retain
the literal mass and differential integrals on smooth sections. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaGlobalInclusion_test_norm_sq (F : cubicThetaSmoothTests) :
    ‖cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)‖^2=
      ∫ q, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure := by
  rw [cubicThetaGlobalInclusion_test,cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [(cubicThetaSectionRepresentative_memLp F).coeFn_toLp] with q hq
  change ‖((cubicThetaSectionRepresentative_memLp F).toLp _) q‖^2=_
  rw [hq,cubicThetaSectionRepresentative_norm]

lemma cubicThetaGlobalGradient_test_norm_sq (F : cubicThetaSmoothTests) :
    ‖cubicThetaGlobalEnergyGradient (cubicThetaGlobalEnergyTest F)‖^2=
      ∫ q, cubicThetaQuotientEnergy F q ∂cubicThetaQuotientMeasure := by
  rw [cubicThetaGlobalEnergyGradient_test,cubicTheta_l2_norm_sq_measure]
  apply integral_congr_ae
  filter_upwards [(cubicThetaGradientRepresentative_memLp F).coeFn_toLp] with q hq
  change ‖((cubicThetaGradientRepresentative_memLp F).toLp _) q‖^2=_
  rw [hq]
  change ‖cubicThetaSectionGradient F (cubicThetaBorelSection q)‖^2=_
  rw [cubicThetaSectionGradient_norm_sq,← cubicThetaQuotientEnergy_apply,
    cubicThetaBorelSection_rightInverse]

lemma cubicThetaCoreRestriction_test_norm_sq (S : Finset SL(2,Eisenstein)) (V : ℝ)
    (F : cubicThetaSmoothTests) :
    ‖cubicThetaCoreRestriction S V (cubicThetaGlobalEnergyTest F)‖^2=
      ∫ q in cubicThetaQuotientCore S V, cubicThetaSectionNorm F q^2
        ∂cubicThetaQuotientMeasure := by
  let K := cubicThetaQuotientCore S V
  have hK : MeasurableSet K := (cubicThetaQuotientCore_compact S V).measurableSet
  rw [cubicTheta_l2_norm_sq_measure,← integral_indicator hK]
  apply integral_congr_ae
  filter_upwards [cubicThetaGlobalRestriction_ae hK
    (cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)),
    (cubicThetaSectionRepresentative_memLp F).coeFn_toLp] with q hr hq
  change ‖cubicThetaGlobalRestriction hK
    (cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)) q‖^2=_
  rw [hr]
  by_cases hk : q∈K
  · rw [indicator_of_mem hk,indicator_of_mem hk]
    change ‖((cubicThetaSectionRepresentative_memLp F).toLp _) q‖^2=_
    rw [hq,cubicThetaSectionRepresentative_norm]
  · rw [indicator_of_notMem hk,indicator_of_notMem hk,norm_zero,
      zero_pow (by norm_num : (2:ℕ)≠0)]

end CubicFirstMoment

end

end OAI
