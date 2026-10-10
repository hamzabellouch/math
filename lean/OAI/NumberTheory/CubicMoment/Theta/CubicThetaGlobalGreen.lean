import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalWeakInverse
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveContraction
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! The positive global Green operator is constructed from the actual
energy inclusion. Its resolvent is analytic off the nonnegative spectral
axis; continuation across that axis is a separate step. -/
noncomputable section
open scoped InnerProduct
namespace CubicFirstMoment

lemma cubicThetaGlobalWeakSolution_eq_adjoint (F : CubicThetaGlobalL2) :
    cubicThetaGlobalWeakSolution F=cubicThetaGlobalInclusion.adjoint F := by
  symm
  apply cubicThetaGlobalWeakSolution_unique F
  intro v
  exact cubicThetaGlobalInclusion.adjoint_inner_left v F

def cubicThetaGlobalGreen : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 :=
  cubicThetaGlobalInclusion.comp cubicThetaGlobalInclusion.adjoint

lemma cubicThetaGlobalGreen_apply (F : CubicThetaGlobalL2) :
    cubicThetaGlobalGreen F=cubicThetaGlobalInclusion (cubicThetaGlobalWeakSolution F) := by
  rw [cubicThetaGlobalWeakSolution_eq_adjoint]
  rfl

lemma cubicThetaGlobalGreen_norm : ‖cubicThetaGlobalGreen‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro F
  rw [cubicThetaGlobalGreen_apply]
  simpa only [one_mul] using (cubicThetaGlobalInclusion_bound _).trans
    (cubicThetaGlobalWeakSolution_bound F)

lemma cubicThetaGlobalGreen_positive : cubicThetaGlobalGreen.IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint cubicThetaGlobalInclusion

lemma cubicThetaGlobalGreen_energy (F : CubicThetaGlobalL2) :
    (inner ℂ F (cubicThetaGlobalGreen F)).re=‖cubicThetaGlobalWeakSolution F‖^2 := by
  rw [cubicThetaGlobalGreen_apply,← cubicThetaGlobalWeakSolution_equation]
  exact inner_self_eq_norm_sq (𝕜:=ℂ) (cubicThetaGlobalWeakSolution F)

lemma cubicThetaGlobalGreen_unit {z : ℂ} (hz : z.im≠0 ∨ z.re<1) :
    IsUnit (1-z • cubicThetaGlobalGreen) :=
  cubicThetaPositiveContraction_unit cubicThetaGlobalGreen cubicThetaGlobalGreen_positive
    cubicThetaGlobalGreen_norm hz

def cubicThetaGlobalResolvent (z : ℂ) : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 :=
  Ring.inverse (1-z • cubicThetaGlobalGreen)*cubicThetaGlobalGreen

lemma cubicThetaGlobalResolvent_analytic {z : ℂ} (hz : z.im≠0 ∨ z.re<1) :
    AnalyticAt ℂ cubicThetaGlobalResolvent z := by
  have hu := cubicThetaGlobalGreen_unit hz
  have hi : AnalyticAt ℂ Ring.inverse (1-z • cubicThetaGlobalGreen) := by
    convert analyticAt_inverse (𝕜:=ℂ) hu.unit using 1
    exact hu.unit_spec
  have ha : AnalyticAt ℂ (fun w : ℂ => 1-w • cubicThetaGlobalGreen) z :=
    analyticAt_const.sub (analyticAt_id.smul analyticAt_const)
  exact (hi.comp (f:=fun w : ℂ => 1-w • cubicThetaGlobalGreen) (x:=z) ha).mul analyticAt_const

lemma cubicThetaGlobalResolvent_identity {z : ℂ} (hz : z.im≠0 ∨ z.re<1) :
    (1-z • cubicThetaGlobalGreen)*cubicThetaGlobalResolvent z=cubicThetaGlobalGreen := by
  unfold cubicThetaGlobalResolvent
  rw [← mul_assoc,Ring.mul_inverse_cancel _ (cubicThetaGlobalGreen_unit hz),one_mul]

lemma cubicThetaGlobalResolvent_range {z : ℂ} (hz : z.im≠0 ∨ z.re<1)
    (F : CubicThetaGlobalL2) :
    cubicThetaGlobalResolvent z F=
      cubicThetaGlobalGreen (F+z • cubicThetaGlobalResolvent z F) := by
  have he := congrArg (fun T : CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2 => T F)
    (cubicThetaGlobalResolvent_identity hz)
  have he' : cubicThetaGlobalResolvent z F-z •
      cubicThetaGlobalGreen (cubicThetaGlobalResolvent z F)=cubicThetaGlobalGreen F := he
  rw [map_add,map_smul]
  exact sub_eq_iff_eq_add.mp he'

end CubicFirstMoment

end

end OAI
