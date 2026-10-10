import OAI.Geometry.Kahler.BasePatchModel

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma regularizedLog_uniform_bounds (a : ℝ) {ε : ℝ} (hε : ε ≠ 0) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ v : ℂ, ‖v‖ ≤ A → |regularizedLog a ε v| ≤ C) ∧
      ∀ v w : ℂ, ‖v‖ ≤ A → ‖w‖ ≤ A →
        |regularizedLog a ε v-regularizedLog a ε w| ≤ C*‖v-w‖ := by
  have hs := regularizedLog_contDiff a hε
  have hc : Continuous (fderiv ℝ (regularizedLog a ε)) := hs.continuous_fderiv (by norm_num)
  obtain ⟨L,hL⟩ := (isCompact_closedBall (0:ℂ) A).bddAbove_image hc.norm.continuousOn
  let B := max L 0
  have hB : 0 ≤ B := le_max_right _ _
  have hb : ∀ x ∈ Metric.closedBall (0:ℂ) A, ‖fderiv ℝ (regularizedLog a ε) x‖ ≤ B := by
    intro x hx
    exact (hL (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hlip : ∀ v w : ℂ, ‖v‖ ≤ A → ‖w‖ ≤ A → |regularizedLog a ε v-regularizedLog a ε w| ≤ B*‖v-w‖ := by
    intro v w hv hw
    have hm := (convex_closedBall (0:ℂ) A).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hs.differentiable (by norm_num) x) hb
      (show w ∈ Metric.closedBall 0 A by simpa using hw)
      (show v ∈ Metric.closedBall 0 A by simpa using hv)
    simpa only [Real.norm_eq_abs] using hm
  refine ⟨B*(1+A),by positivity,?_,?_⟩
  · intro v hv
    have hh := hlip v 0 hv (by simpa using hA)
    simp only [regularizedLog_zero,sub_zero] at hh
    exact hh.trans (by gcongr; linarith)
  · intro v w hv hw
    exact (hlip v w hv hw).trans (by gcongr; nlinarith)

end PinchedHartogs.BaseConstruction

end

end OAI
