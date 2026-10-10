import Mathlib

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def pathExtension (u : C(unitInterval, E)) : C(ℝ, E) :=
  u.comp ⟨projIcc 0 1 zero_le_one, continuous_projIcc⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] lemma pathExtension_apply (u : C(unitInterval, E)) (t : ℝ) :
    pathExtension u t = u (projIcc 0 1 zero_le_one t) := rfl

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma pathExtension_coe (u : C(unitInterval, E)) (s : unitInterval) :
    pathExtension u s = u s := by
  simp only [pathExtension_apply, projIcc_val]

def volterra : C(unitInterval, E) →L[ℝ] C(unitInterval, E) := by
  let L : C(unitInterval, E) →ₗ[ℝ] C(unitInterval, E) :=
    { toFun := fun u => ⟨fun s => ∫ t in 0..(s : ℝ), pathExtension u t,
        (continuous_primitive (fun a b => (pathExtension u).continuous.intervalIntegrable a b) 0).comp
          continuous_subtype_val⟩
      map_add' := fun u v => by
        ext s
        exact integral_add ((pathExtension u).continuous.intervalIntegrable _ _)
          ((pathExtension v).continuous.intervalIntegrable _ _)
      map_smul' := fun c u => by ext s; exact integral_smul c (pathExtension u) }
  apply L.mkContinuous 1
  intro u
  rw [one_mul]
  apply (ContinuousMap.norm_le (L u) (norm_nonneg u)).mpr
  intro s
  change ‖∫ t in 0..(s : ℝ), pathExtension u t‖ ≤ ‖u‖
  apply (norm_integral_le_of_norm_le_const (fun t _ => u.norm_coe_le_norm _)).trans
  rw [sub_zero, abs_of_nonneg s.property.1]
  exact mul_le_of_le_one_right (norm_nonneg _) s.property.2

omit [CompleteSpace E] in
@[simp] lemma volterra_apply (u : C(unitInterval, E)) (s : unitInterval) :
    volterra u s = ∫ t in 0..(s : ℝ), pathExtension u t := rfl

omit [CompleteSpace E] in
@[simp] lemma volterra_zero (u : C(unitInterval, E)) : volterra u 0 = 0 := by simp

omit [CompleteSpace E] in
lemma volterra_norm_le : ‖volterra (E := E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  apply (ContinuousMap.norm_le (volterra u) (norm_nonneg u)).mpr
  intro s
  apply (norm_integral_le_of_norm_le_const (fun t _ => u.norm_coe_le_norm _)).trans
  rw [sub_zero, abs_of_nonneg s.property.1]
  exact mul_le_of_le_one_right (norm_nonneg _) s.property.2

lemma hasDerivAt_volterra_extension (u : C(unitInterval, E)) (s : ℝ) :
    HasDerivAt (fun r => ∫ t in 0..r, pathExtension u t) (pathExtension u s) s := by
  apply integral_hasDerivAt_right
  · exact (pathExtension u).continuous.intervalIntegrable _ _
  · exact (pathExtension u).continuous.stronglyMeasurableAtFilter _ _
  · exact (pathExtension u).continuous.continuousAt

end YauCounterexamples

end

end OAI
