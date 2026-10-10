import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.FlowParameters

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
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
open Set Filter Function Metric
open scoped Topology ContDiff NNReal
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma integral_path_eq_solution {V : E → E} {K : ℝ≥0} (hV : LipschitzWith K V)
    {y : E} {t ε : ℝ} (ht : |t| < ε) (u : C(unitInterval, E))
    (hu : u = ContinuousMap.const unitInterval y + t • volterra (superposition V hV.continuous u))
    (α : ℝ → E) (hα0 : α 0 = y)
    (hα : ∀ r ∈ Ioo (-ε) ε, HasDerivAt α (V (α r)) r) :
    ∀ s : unitInterval, u s = α (t * (s : ℝ)) := by
  let w := superposition V hV.continuous u
  let β : ℝ → E := fun s => y + t • ∫ r in 0..s, pathExtension w r
  have hβeq (s : unitInterval) : β s = u s := by
    have hh := congrArg (fun v : C(unitInterval,E) => v s) hu
    exact hh.symm
  have hts (s : ℝ) (hs : s ∈ Icc 0 1) : t*s ∈ Ioo (-ε) ε := by
    have h : |t*s| ≤ |t| := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_right (abs_nonneg _) hs.2
    exact abs_lt.mp (h.trans_lt ht)
  have hβd (s : ℝ) : HasDerivAt β (t • pathExtension w s) s := by
    exact (hasDerivAt_volterra_extension w s).const_smul t |>.const_add y
  have hβc : Continuous β := continuous_iff_continuousAt.mpr fun s => (hβd s).continuousAt
  have hγd (s : ℝ) (hs : s ∈ Icc 0 1) :
      HasDerivAt (fun r => α (t*r)) (t • V (α (t*s))) s := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (hα _ (hts s hs)).scomp s ((hasDerivAt_id s).const_mul t)
  have hγc : ContinuousOn (fun r => α (t*r)) (Icc 0 1) :=
    fun s hs => (hγd s hs).continuousAt.continuousWithinAt
  have he := ODE_solution_unique (v := fun _ z => t • V z)
    (fun _ => (t • ContinuousLinearMap.id ℝ E).lipschitzWith.comp hV) hβc.continuousOn
    (fun s hs => ?_) hγc (fun s hs => (hγd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (show β 0 = α (t*0) by simp [β,hα0])
  · intro s
    rw [← hβeq s]
    exact he s.property
  · have hs' : s ∈ Icc 0 1 := Ico_subset_Icc_self hs
    have hw : pathExtension w s = V (β s) := by
      rw [← (show (⟨s,hs'⟩ : unitInterval).val = s from rfl), pathExtension_coe, hβeq]
      rfl
    have hh := hβd s
    rw [hw] at hh
    exact hh.hasDerivWithinAt
end YauCounterexamples

end

end OAI
