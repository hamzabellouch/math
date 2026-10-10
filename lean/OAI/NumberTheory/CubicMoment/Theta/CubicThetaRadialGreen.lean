import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialRiesz
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-! The bounded positive Green operator of the radial Dirichlet form and
its actual local resolvent. This is constructed from the energy space. -/
noncomputable section
open scoped InnerProduct
namespace CubicFirstMoment

lemma cubicThetaRadialWeakSolution_eq_adjoint (A : ℝ) (F : CubicThetaRadialL2) :
    cubicThetaRadialWeakSolution A F=(cubicThetaRadialInclusion A).adjoint F := by
  symm
  apply cubicThetaRadialWeakSolution_unique A F
  intro v
  exact (cubicThetaRadialInclusion A).adjoint_inner_left v F

def cubicThetaRadialGreen (A : ℝ) : CubicThetaRadialL2 →L[ℂ] CubicThetaRadialL2 :=
  (cubicThetaRadialInclusion A).comp (cubicThetaRadialInclusion A).adjoint

lemma cubicThetaRadialGreen_apply (A : ℝ) (F : CubicThetaRadialL2) :
    cubicThetaRadialGreen A F=cubicThetaRadialInclusion A (cubicThetaRadialWeakSolution A F) := by
  rw [cubicThetaRadialWeakSolution_eq_adjoint]
  rfl

lemma cubicThetaRadialGreen_norm (A : ℝ) : ‖cubicThetaRadialGreen A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro F
  rw [cubicThetaRadialGreen_apply]
  exact (cubicThetaRadialCoordinate_bound A 0 _).trans
    (by simpa using cubicThetaRadialWeakSolution_bound A F)

lemma cubicThetaRadialGreen_selfAdjoint (A : ℝ) : IsSelfAdjoint (cubicThetaRadialGreen A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp only [cubicThetaRadialGreen,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

lemma cubicThetaRadialGreen_energy (A : ℝ) (F : CubicThetaRadialL2) :
    (inner ℂ F (cubicThetaRadialGreen A F)).re=‖cubicThetaRadialWeakSolution A F‖^2 := by
  rw [cubicThetaRadialGreen_apply,← cubicThetaRadialWeakSolution_equation]
  exact inner_self_eq_norm_sq (𝕜:=ℂ) (cubicThetaRadialWeakSolution A F)

lemma cubicThetaRadialGreen_one_sub_unit (A : ℝ) {z : ℂ} (hz : ‖z‖<1) :
    IsUnit (1-z • cubicThetaRadialGreen A) := by
  apply isUnit_one_sub_of_norm_lt_one
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (cubicThetaRadialGreen_norm A) (_root_.norm_nonneg z)).trans_lt
    (by simpa using hz)

def cubicThetaRadialResolvent (A : ℝ) (z : ℂ) :
    CubicThetaRadialL2 →L[ℂ] CubicThetaRadialL2 :=
  Ring.inverse (1-z • cubicThetaRadialGreen A)*cubicThetaRadialGreen A

lemma cubicThetaRadialResolvent_analytic (A : ℝ) {z : ℂ} (hz : ‖z‖<1) :
    AnalyticAt ℂ (cubicThetaRadialResolvent A) z := by
  have hu := cubicThetaRadialGreen_one_sub_unit A hz
  have hi : AnalyticAt ℂ Ring.inverse (1-z • cubicThetaRadialGreen A) := by
    convert analyticAt_inverse (𝕜:=ℂ) hu.unit using 1
    exact hu.unit_spec
  have ha : AnalyticAt ℂ (fun w : ℂ => 1-w • cubicThetaRadialGreen A) z :=
    analyticAt_const.sub (analyticAt_id.smul analyticAt_const)
  exact (hi.comp (f:=fun w : ℂ => 1-w • cubicThetaRadialGreen A) (x:=z) ha).mul analyticAt_const

lemma cubicThetaRadialResolvent_identity (A : ℝ) {z : ℂ} (hz : ‖z‖<1) :
    (1-z • cubicThetaRadialGreen A)*cubicThetaRadialResolvent A z=cubicThetaRadialGreen A := by
  unfold cubicThetaRadialResolvent
  rw [← mul_assoc,Ring.mul_inverse_cancel _ (cubicThetaRadialGreen_one_sub_unit A hz),one_mul]

end CubicFirstMoment

end

end OAI
