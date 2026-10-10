import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.FlowPointwise
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

namespace OAI

/-! Integration on the fixed unit interval as a bounded linear operator.
This permits elapsed time to be a parameter of the Picard equation. -/

noncomputable section
namespace ForcedComputation.Flow
open Set MeasureTheory
open scoped Topology

abbrev UnitTime := Icc (0 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def extendPath (u : C(UnitTime, E)) : C(ℝ, E) :=
  u.comp ⟨projIcc 0 1 zero_le_one, continuous_projIcc⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem extendPath_apply (u : C(UnitTime, E)) (t : ℝ) :
    extendPath u t = u (projIcc 0 1 zero_le_one t) := rfl

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem extendPath_coe (u : C(UnitTime, E)) (t : UnitTime) :
    extendPath u t = u t := by simp [extendPath]

def primitivePath (u : C(UnitTime, E)) : C(UnitTime, E) :=
  ⟨fun t => ∫ s in (0 : ℝ)..t.1, extendPath u s,
    (continuous_iff_continuousAt.mpr fun t =>
      ((extendPath u).continuous.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt).comp
        continuous_subtype_val⟩

@[simp] theorem primitivePath_apply (u : C(UnitTime, E)) (t : UnitTime) :
    primitivePath u t = ∫ s in (0 : ℝ)..t.1, extendPath u s := rfl

theorem primitivePath_norm (u : C(UnitTime, E)) : ‖primitivePath u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro t
  calc
    ‖primitivePath u t‖ ≤ ‖u‖ * |t.1 - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun s _ =>
        u.norm_coe_le_norm _
    _ ≤ ‖u‖ := by
      rw [sub_zero, abs_of_nonneg t.2.1]
      exact mul_le_of_le_one_right (norm_nonneg u) t.2.2

def primitivePathL : C(UnitTime, E) →L[ℝ] C(UnitTime, E) :=
  LinearMap.mkContinuous
    { toFun := primitivePath
      map_add' := by
        intro u v
        ext t
        change (∫ s in (0 : ℝ)..t.1, extendPath u s + extendPath v s) = _
        exact intervalIntegral.integral_add
          ((extendPath u).continuous.intervalIntegrable _ _)
          ((extendPath v).continuous.intervalIntegrable _ _)
      map_smul' := by
        intro c u
        ext t
        change (∫ s in (0 : ℝ)..t.1, c • extendPath u s) = _
        exact intervalIntegral.integral_smul c (extendPath u) }
    1 (by
      intro u
      change ‖primitivePath u‖ ≤ (1 : ℝ) * ‖u‖
      rw [one_mul]
      exact primitivePath_norm u)

@[simp] theorem primitivePathL_apply (u : C(UnitTime, E)) :
    primitivePathL u = primitivePath u := rfl

theorem primitivePathL_norm : ‖primitivePathL (E := E)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end ForcedComputation.Flow

end

end OAI
