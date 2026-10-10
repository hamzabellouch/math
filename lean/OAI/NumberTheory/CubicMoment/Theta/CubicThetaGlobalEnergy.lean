import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalGradient
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialEnergyNorm

namespace OAI

/-! The global energy completion of genuine compact smooth cubic
sections. Its two coordinates are the value and the actual gradient. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

abbrev CubicThetaGlobalEnergyAmbient := WithLp 2 (CubicThetaGlobalL2 × CubicThetaGradientL2)

def cubicThetaGlobalEnergyGraph : cubicThetaSmoothTests →ₗ[ℂ] CubicThetaGlobalEnergyAmbient :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2).symm.toLinearMap.comp
    (cubicThetaGlobalMass.prod cubicThetaGlobalGradient)

def cubicThetaGlobalEnergySpace : Submodule ℂ CubicThetaGlobalEnergyAmbient :=
  cubicThetaGlobalEnergyGraph.range.topologicalClosure

instance cubicThetaGlobalEnergySpace_complete : CompleteSpace cubicThetaGlobalEnergySpace :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def cubicThetaGlobalEnergyTest (F : cubicThetaSmoothTests) : cubicThetaGlobalEnergySpace :=
  ⟨cubicThetaGlobalEnergyGraph F,Submodule.le_topologicalClosure _ ⟨F,rfl⟩⟩

def cubicThetaGlobalInclusion : cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaGlobalL2 :=
  (WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2).comp
    cubicThetaGlobalEnergySpace.subtypeL

def cubicThetaGlobalEnergyGradient : cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaGradientL2 :=
  (WithLp.sndL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2).comp
    cubicThetaGlobalEnergySpace.subtypeL

lemma cubicThetaGlobalInclusion_test (F : cubicThetaSmoothTests) :
    cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F)=cubicThetaGlobalMass F := rfl

lemma cubicThetaGlobalEnergyGradient_test (F : cubicThetaSmoothTests) :
    cubicThetaGlobalEnergyGradient (cubicThetaGlobalEnergyTest F)=cubicThetaGlobalGradient F := rfl

lemma cubicThetaGlobalInclusion_bound (u : cubicThetaGlobalEnergySpace) :
    ‖cubicThetaGlobalInclusion u‖≤‖u‖ := WithLp.norm_fst_le CubicThetaGlobalL2 (u:CubicThetaGlobalEnergyAmbient)

lemma cubicThetaGlobalInclusion_norm : ‖cubicThetaGlobalInclusion‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using cubicThetaGlobalInclusion_bound u

lemma cubicThetaGlobalEnergy_norm_sq (u : cubicThetaGlobalEnergySpace) :
    ‖u‖^2=‖cubicThetaGlobalInclusion u‖^2+‖cubicThetaGlobalEnergyGradient u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 (u:CubicThetaGlobalEnergyAmbient)

lemma cubicThetaGlobalEnergyTest_norm_sq (F : cubicThetaSmoothTests) :
    ‖cubicThetaGlobalEnergyTest F‖^2=
      ∫ q, ‖cubicThetaSectionRepresentative F q‖^2+cubicThetaQuotientEnergy F q
        ∂cubicThetaQuotientMeasure := by
  rw [cubicThetaGlobalEnergy_norm_sq,cubicThetaGlobalInclusion_test,
    cubicThetaGlobalEnergyGradient_test]
  have hM : Integrable (fun q => ‖cubicThetaSectionRepresentative F q‖^2)
      cubicThetaQuotientMeasure := (cubicThetaSectionRepresentative_memLp F).integrable_norm_pow (by norm_num)
  have hG : Integrable (fun q => ‖cubicThetaGradientRepresentative F q‖^2)
      cubicThetaQuotientMeasure := (cubicThetaGradientRepresentative_memLp F).integrable_norm_pow (by norm_num)
  have he : (fun q => ‖cubicThetaGradientRepresentative F q‖^2)=cubicThetaQuotientEnergy F := by
    funext q
    change ‖cubicThetaSectionGradient F (cubicThetaBorelSection q)‖^2=_
    rw [cubicThetaSectionGradient_norm_sq,← cubicThetaQuotientEnergy_apply,
      cubicThetaBorelSection_rightInverse]
  rw [cubicTheta_l2_norm_sq_measure,cubicTheta_l2_norm_sq_measure]
  have h₁ : (fun q => ‖(cubicThetaGlobalMass F) q‖^2) =ᵐ[cubicThetaQuotientMeasure]
      (fun q => ‖cubicThetaSectionRepresentative F q‖^2) := by
    filter_upwards [(cubicThetaSectionRepresentative_memLp F).coeFn_toLp] with q hq
    change ‖((cubicThetaSectionRepresentative_memLp F).toLp _) q‖^2=_
    rw [hq]
  have h₂ : (fun q => ‖(cubicThetaGlobalGradient F) q‖^2) =ᵐ[cubicThetaQuotientMeasure]
      (fun q => ‖cubicThetaGradientRepresentative F q‖^2) := by
    filter_upwards [(cubicThetaGradientRepresentative_memLp F).coeFn_toLp] with q hq
    change ‖((cubicThetaGradientRepresentative_memLp F).toLp _) q‖^2=_
    rw [hq]
  rw [integral_congr_ae h₁,integral_congr_ae h₂,← integral_add hM hG]
  apply integral_congr_ae
  filter_upwards with q
  rw [congrFun he q]

end CubicFirstMoment

end

end OAI
