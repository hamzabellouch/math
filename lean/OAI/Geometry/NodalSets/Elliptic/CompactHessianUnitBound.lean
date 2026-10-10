import OAI.Geometry.NodalSets.Charts.CorrugationFrameBounds
import OAI.Geometry.NodalSets.Elliptic.CorrugationOldData

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

theorem compact_sourceHessian_unit_bound
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    {D U : Set Coord} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ D, ∀ u v : Coord,
      g x u u = 1 → g x v v = 1 → |sourceHessian g S x u v| ≤ C := by
  have hcH : ContinuousOn (sourceHessian g S) D := by
    intro y hy
    exact (localMetricHessian_continuousAt g S y
      (hg.contDiffAt (hU.mem_nhds (hDU hy))) (hS.contDiffAt (hU.mem_nhds (hDU hy)))
      (hp y (hDU hy))).continuousWithinAt
  obtain ⟨H,hH,hHB⟩ := (hD.image_of_continuousOn hcH).isBounded.exists_pos_norm_le
  obtain ⟨c,hc,M,hM,hmetric⟩ := compact_metric_comparison g hD (hg.continuousOn.mono hDU)
    (fun y hy ↦ hp y (hDU hy))
  refine ⟨H*(1+c⁻¹)^2,by positivity,?_⟩
  intro x hx u v hu hv
  have huB := metric_unit_coordinate_bound (g x) hc (hmetric x hx).2 u hu
  have hvB := metric_unit_coordinate_bound (g x) hc (hmetric x hx).2 v hv
  calc
    _ ≤ ‖sourceHessian g S x‖*‖u‖*‖v‖ := bilinear_pairing_bound _ _ _
    _ ≤ H*(1+c⁻¹)*(1+c⁻¹) := by gcongr; exact hHB _ ⟨x,hx,rfl⟩
    _ = _ := by ring

end
end Yau.Geometry

end OAI
