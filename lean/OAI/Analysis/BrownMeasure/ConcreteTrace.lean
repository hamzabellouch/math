import Mathlib
import OAI.Analysis.BrownMeasure.Model
import OAI.Analysis.BrownMeasure.Quasinilpotent
import OAI.Analysis.FiniteFactor.CrossedProduct.Trace
import OAI.Analysis.FiniteFactor.CrossedProduct.WeightedShiftField

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology Ring
namespace FiniteFactor
abbrev SourceCStar (θ : SourceCoordinate → ℝ) := (sourceAlgebra θ).toStarSubalgebra
instance sourceCStar_closed (θ : SourceCoordinate → ℝ) : IsClosed (SourceCStar θ:Set ProductOp) := by
  change IsClosed (sourceAlgebra θ:Set ProductOp)
  rw [← (sourceAlgebra θ).centralizer_centralizer]
  exact Set.isClosed_centralizer _
instance sourceCStar_nontrivial (θ : SourceCoordinate → ℝ) : Nontrivial (SourceCStar θ) := by
  exact nontrivial_of_ne (0 : SourceCStar θ) 1
    (fun equality => zero_ne_one (congrArg Subtype.val equality))
local instance (θ : SourceCoordinate → ℝ) : IsometricContinuousFunctionalCalculus ℝ (SourceCStar θ) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
local instance : IsometricContinuousFunctionalCalculus ℝ ProductOp IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

def sourceRealTrace (θ : SourceCoordinate → ℝ) : SourceCStar θ →L[ℝ] ℝ :=
  (show SourceCStar θ →ₗ[ℝ] ℝ from {
    toFun := fun a=>(sourceVacuumFunctional a).re
    map_add' := fun a b=>by simp [sourceVacuumFunctional_add]
    map_smul' := fun a b=>by
      change (sourceVacuumFunctional (((a:ℂ) • (b:ProductOp)))).re=a*(sourceVacuumFunctional b).re
      rw [sourceVacuumFunctional_smul]
      simp
  }).mkContinuous 1 (fun a=>by
    change |(sourceVacuumFunctional a).re|≤1*‖(a:ProductOp)‖
    simpa only [one_mul] using (Complex.abs_re_le_norm (sourceVacuumFunctional a)).trans (sourceVacuumFunctional_bound a))
lemma sourceRealTrace_apply (θ : SourceCoordinate → ℝ) (a : SourceCStar θ) :
    sourceRealTrace θ a=(sourceVacuumFunctional a).re := rfl
lemma sourceRealTrace_cyclic (θ : SourceCoordinate → ℝ) (a b : SourceCStar θ) :
    sourceRealTrace θ (a*b)=sourceRealTrace θ (b*a) :=
  congrArg Complex.re (sourceVacuumFunctional_tracial θ a.property b.property)
lemma sourceRealTrace_star (θ : SourceCoordinate → ℝ) (a : SourceCStar θ) :
    sourceRealTrace θ (star a)=sourceRealTrace θ a := by
  change (inner ℂ sourceVacuum ((star (a:ProductOp)) sourceVacuum)).re=(sourceVacuumFunctional a).re
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  rw [← inner_conj_symm]
  rfl
lemma sourceOperator_trace_pow_zero (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℕ) :
    sourceVacuumFunctional (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg^(n+1))=0 := by
  rw [sourceVacuumFunctional_matrixIntegral]
  have he : (fun x=>sourceMatrixEntry (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg^(n+1)) 0 0 x)=ᵐ[sourceBaseMeasure] fun _=>0 := by
    filter_upwards [sourceMatrixEntry_sourceOperator_pow θ hθ (n+1) 0] with x hx
    rw [hx,ite_eq_right (by omega)]
  rw [integral_congr_ae he,integral_zero]

def sourceCStarOperator (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) : SourceCStar θ :=
  ⟨sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg,staged_sourceOperator_mem θ hθ⟩

lemma sourceCStarOperator_root (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    Tendsto (fun n:ℕ=>‖sourceCStarOperator θ hθ^n‖^(1/(n:ℝ))) atTop (𝓝 0) :=
  (staged_sourceOperator_properties θ hθ).2.2.2

lemma sourceOperator_one_sub_isUnit (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (c : ℂ) :
    IsUnit (1-c•sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg) :=
  (BrownLog.inverse_one_sub_eq_tsum _ (BrownLog.summable_pow_of_root_tendsto _
    (BrownLog.norm_root_smul_tendsto _ c (staged_sourceOperator_properties θ hθ).2.2.2))).1

lemma sourceOperator_trace_log_square_one_sub (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (c : ℂ) :
    (sourceVacuumFunctional (CFC.log (star (1-c•sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)*
      (1-c•sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)))).re=0 := by
  let S : SourceCStar θ := c•sourceCStarOperator θ hθ
  have hQ := BrownLog.norm_root_smul_tendsto _ c (sourceCStarOperator_root θ hθ)
  have hz (n : ℕ) : sourceRealTrace θ (S^(n+1))=0 := by
    change (sourceVacuumFunctional ((c•sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)^(n+1))).re=0
    rw [smul_pow,sourceVacuumFunctional_smul,sourceOperator_trace_pow_zero θ hθ,mul_zero,Complex.zero_re]
  have H := BrownLog.trace_log_square_one_sub_eq_zero (sourceRealTrace θ) (sourceRealTrace_cyclic θ)
    (sourceRealTrace_star θ) S hQ hz
  let φ := (sourceAlgebra θ).toStarSubalgebra.subtype
  have hu : IsUnit (1-S) := (BrownLog.inverse_one_sub_eq_tsum _ (BrownLog.summable_pow_of_root_tendsto _ hQ)).1
  have hi : IsUnit (star (1-S)*(1-S)) := hu.star.mul hu
  have hs : IsSelfAdjoint (star (1-S)*(1-S)) := isSelfAdjoint_iff.mpr (by simp)
  have hc : ContinuousOn Real.log (spectrum ℝ (star (1-S)*(1-S))) := by
    apply Real.continuousOn_log.mono
    intro y hy
    exact fun h=>(spectrum.zero_notMem ℝ hi) (h ▸ hy)
  have he := φ.map_cfc Real.log (star (1-S)*(1-S)) hc continuous_subtype_val hs (hs.map φ)
  change (sourceVacuumFunctional (φ (cfc Real.log (star (1-S)*(1-S))))).re=0 at H
  rw [he] at H
  exact H
end FiniteFactor
end

end OAI
