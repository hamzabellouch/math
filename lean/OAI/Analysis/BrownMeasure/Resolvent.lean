import Mathlib
import OAI.Analysis.BrownMeasure.ConcreteTrace
import OAI.Analysis.BrownMeasure.UnitDeterminant

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology Ring ENNReal
namespace FiniteFactor
local instance resolventRealModule : Module ℝ ProductOp := Module.complexToReal ProductOp
local instance resolventFunctionalCalculus :
    IsometricContinuousFunctionalCalculus ℝ ProductOp IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

lemma sourceResolvent_factor (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) {z : ℂ} (hz : z≠0) :
    sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg-algebraMap ℂ ProductOp z =
    (-z)•(1-z⁻¹•sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg) := by
  rw [smul_sub,smul_smul,neg_mul,mul_inv_cancel₀ hz,neg_one_smul (M := ProductOp) ℂ]
  rw [← Algebra.algebraMap_eq_smul_one, map_neg]
  abel

lemma sourceResolvent_isUnit (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) {z : ℂ} (hz : z≠0) :
    IsUnit (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg-algebraMap ℂ ProductOp z) := by
  rw [sourceResolvent_factor θ hθ hz,Algebra.smul_def (A := ProductOp) (-z)]
  exact ((isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hz)).map (algebraMap ℂ ProductOp)).mul
    (sourceOperator_one_sub_isUnit θ hθ z⁻¹)

lemma sourceVacuumFunctional_algebraMap_real (r : ℝ) :
    (sourceVacuumFunctional (algebraMap ℝ ProductOp r)).re=r := by
  rw [Algebra.algebraMap_eq_smul_one]
  change (sourceVacuumFunctional ((r:ℂ)•(1:ProductOp))).re=r
  rw [sourceVacuumFunctional_smul,sourceVacuumFunctional_one,mul_one,Complex.ofReal_re]

lemma sourceResolvent_trace_log_square (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) {z : ℂ} (hz : z≠0) :
    (sourceVacuumFunctional (CFC.log (star (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg-algebraMap ℂ ProductOp z)*
      (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg-algebraMap ℂ ProductOp z)))).re=2*Real.log ‖z‖ := by
  let A : ProductOp := 1-z⁻¹•sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
  have hu : IsUnit A := sourceOperator_one_sub_isUnit θ hθ z⁻¹
  have hn : ∀y∈spectrum ℝ (star A*A),y≠0 := by
    intro y hy he
    exact spectrum.zero_notMem ℝ (hu.star.mul hu) (he ▸ hy)
  have hs : IsSelfAdjoint (star A*A) := isSelfAdjoint_iff.mpr (by simp)
  have he : star ((-z)•A)*((-z)•A)=(‖z‖^2:ℝ)•(star A*A) := by
    rw [star_smul,smul_mul_smul_comm,star_neg,neg_mul_neg]
    change ((starRingEnd ℂ) z*z)•(star A*A)=_
    rw [Complex.conj_mul',← Complex.ofReal_pow]
    rfl
  rw [sourceResolvent_factor θ hθ hz]
  change (sourceVacuumFunctional (CFC.log (star ((-z)•A)*((-z)•A)))).re=_
  rw [he]
  have hlog : CFC.log ((‖z‖^2:ℝ)•(star A*A))=
      algebraMap ℝ ProductOp (Real.log (‖z‖^2))+CFC.log (star A*A) :=
    CFC.log_smul (r:=‖z‖^2) (star A*A) hn (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)) hs
  rw [hlog,sourceVacuumFunctional_add,Complex.add_re,sourceVacuumFunctional_algebraMap_real]
  rw [sourceOperator_trace_log_square_one_sub θ hθ z⁻¹,add_zero,Real.log_pow]
  norm_num

lemma sourceResolvent_trace_log_abs (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) {z : ℂ} (hz : z≠0) :
    (sourceVacuumFunctional (CFC.log (CFC.abs (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg-algebraMap ℂ ProductOp z)))).re=Real.log ‖z‖ := by
  let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg-algebraMap ℂ ProductOp z
  have hu : IsUnit T := sourceResolvent_isUnit θ hθ hz
  have hn : ∀y∈spectrum ℝ (CFC.abs T),y≠0 := fun y hy=>(product_abs_spectrum_pos hu hy).ne'
  have hh := CFC.log_pow 2 (CFC.abs T) hn (CFC.abs_nonneg T).isSelfAdjoint
  rw [pow_two, CFC.abs_mul_abs] at hh
  have he := congrArg (fun a:ProductOp=>(sourceVacuumFunctional a).re) hh
  rw [sourceResolvent_trace_log_square θ hθ hz] at he
  simp only [two_nsmul,sourceVacuumFunctional_add,Complex.add_re] at he
  change _=_ at he
  linarith

theorem sourceResolvent_determinant (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) {z : ℂ} (hz : z≠0) :
    FugledeKadisonDeterminant sourceVacuumFunctional
      (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg-algebraMap ℂ ProductOp z)=ENNReal.ofReal ‖z‖ := by
  rw [FugledeKadisonDeterminant_of_isUnit _ (sourceResolvent_isUnit θ hθ hz),
    sourceResolvent_trace_log_abs θ hθ hz,Real.exp_log (norm_pos_iff.mpr hz)]
end FiniteFactor
end

end OAI
