import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRankinConvergence
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaModelGlobalL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueNorm

namespace OAI

/-! The scalar Rankin pole paired with the actual global cubic theta section. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProduct
namespace CubicFirstMoment

lemma cubicThetaArithmeticModelPairing_eq (q : CubicThetaQuotient) :
    cubicThetaSectionPairing cubicThetaArithmeticModelSection cubicThetaArithmeticModelSection q=
      (‖cubicThetaSectionRepresentative cubicThetaArithmeticModelSection q‖^2:ℂ) := by
  have h := cubicThetaSectionPairing_apply cubicThetaArithmeticModelSection
    cubicThetaArithmeticModelSection (cubicThetaBorelSection q)
  rw [cubicThetaBorelSection_rightInverse,inner_self_eq_norm_sq_to_K] at h
  exact h

lemma cubicThetaArithmeticModelPairing_integrable :
    Integrable (cubicThetaSectionPairing cubicThetaArithmeticModelSection
      cubicThetaArithmeticModelSection) cubicThetaQuotientMeasure := by
  have hr : Integrable (fun q => ‖cubicThetaSectionRepresentative cubicThetaArithmeticModelSection q‖^2)
      cubicThetaQuotientMeasure :=
    cubicThetaArithmeticModelGlobal_memLp.integrable_norm_pow (by norm_num)
  have h := hr.ofReal (𝕜:=ℂ)
  apply h.congr
  filter_upwards with q
  rw [cubicThetaArithmeticModelPairing_eq]
  norm_cast

lemma cubicThetaArithmeticModelPairing_integral :
    (∫ q,cubicThetaSectionPairing cubicThetaArithmeticModelSection
      cubicThetaArithmeticModelSection q ∂cubicThetaQuotientMeasure)=
      (‖cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue‖^2:ℂ) := by
  rw [←cubicThetaSectionPairing_L2 _ _ cubicThetaArithmeticModelGlobal_memLp
    cubicThetaArithmeticModelGlobal_memLp,cubicThetaArithmeticModelGlobalL2,
    inner_self_eq_norm_sq_to_K]
  norm_cast

def cubicThetaArithmeticRankinMass (σ : ℝ) : ℂ :=
  ∫ q,(cubicThetaScalarRankinKernel σ q:ℂ)*
    cubicThetaSectionPairing cubicThetaArithmeticModelSection
      cubicThetaArithmeticModelSection q ∂cubicThetaQuotientMeasure

theorem cubicThetaArithmeticRankinMass_residue :
    Tendsto (fun σ : ℝ => (σ:ℂ)*cubicThetaArithmeticRankinMass σ) (𝓝[>] 0)
      (𝓝 (((9*Real.sqrt 3/4:ℝ):ℂ)*(cubicThetaConstant:ℂ)^2)) := by
  have h := cubicThetaScalarRankinKernel_integral_limit
    (cubicThetaSectionPairing cubicThetaArithmeticModelSection cubicThetaArithmeticModelSection)
    cubicThetaArithmeticModelPairing_integrable
  have he (σ : ℝ) : (∫ q,(σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ)*
      cubicThetaSectionPairing cubicThetaArithmeticModelSection cubicThetaArithmeticModelSection q
      ∂cubicThetaQuotientMeasure)=(σ:ℂ)*cubicThetaArithmeticRankinMass σ := by
    rw [cubicThetaArithmeticRankinMass,←integral_const_mul]
    congr 1
    funext q
    ring
  simp_rw [he] at h
  rw [cubicThetaArithmeticModelPairing_integral] at h
  have hn := cubicThetaNormalizedArithmeticResidue_norm_identity
  convert h using 1
  congr 1
  calc
    ((9*Real.sqrt 3/4:ℝ):ℂ)*(cubicThetaConstant:ℂ)^2 =
        (1/2:ℂ)*((‖cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue‖^2:ℂ)*
          ((Real.pi:ℂ)^2/(54*principalIdealZeta 2))) := by rw [hn]; push_cast; ring
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
