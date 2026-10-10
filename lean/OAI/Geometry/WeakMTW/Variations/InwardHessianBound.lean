import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.NonconjugateBranches
import OAI.Geometry.WeakMTW.Geodesics.MinimizerCompactness
import OAI.Geometry.WeakMTW.Variations.BranchHessian
import OAI.Geometry.WeakMTW.Coordinates.FocalCoordinates

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem nonconjugate_hessian_lower_near (x : M) {v : TangentSpace (model n) x}
    (hn : Nonconjugate x v) (ξ : TangentSpace (model n) x) :
    ∃ L : ℝ, ∀ᶠ w in 𝓝 v, w ∈ injectivityDomain x → -L ≤ actionHessian x w ξ ξ := by
  let y := exp x v
  obtain ⟨e,he,hev,hes,hei⟩ := pairExpCoordinates_inverse_of_nonfocal x y hn (mem_chart_source (Model n) y)
  have hB := branchHessianDiag_continuous x y e he hes hei hev ξ
  have hlow : ∀ᶠ w in 𝓝 v, branchHessianDiag x y e v ξ-1 < branchHessianDiag x y e w ξ :=
    continuousAt_const.eventually_lt hB (by linarith)
  have hsrc : ∀ᶠ w in 𝓝 v, verticalCoordinates x w ∈ e.source :=
    (verticalCoordinates_smooth x).continuous.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds (by simpa only [verticalCoordinates_eq] using hev))
  refine ⟨1-branchHessianDiag x y e v ξ,?_⟩
  filter_upwards [hlow,hsrc] with w hw hwe hwi
  rw [verticalCoordinates_eq] at hwe
  rw [actionHessian_eq_branch x y e he hes hei hwi hwe ξ]
  linarith

 theorem nonconjugate_inward_hessian_bound (x : M) {v : TangentSpace (model n) x}
    (hm : v ∈ minimizingDomain x) (hn : Nonconjugate x v) (ξ : TangentSpace (model n) x) :
    ∃ L δ : ℝ, 0 < δ ∧ ∀ h, 0 < h → h < δ →
      -L ≤ actionHessian x ((1-h)•v) ξ ξ := by
  obtain ⟨L,hL⟩ := nonconjugate_hessian_lower_near x hn ξ
  have hc : ContinuousAt (fun h : ℝ => (1-h)•v) 0 := (continuousAt_const.sub continuousAt_id).smul continuousAt_const
  have hh : ∀ᶠ h in 𝓝 (0 : ℝ), (1-h)•v ∈ injectivityDomain x →
      -L ≤ actionHessian x ((1-h)•v) ξ ξ := by
    have hc' : Tendsto (fun h : ℝ => (1-h)•v) (𝓝 0) (𝓝 v) := by simpa using hc.tendsto
    exact hc' hL
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨L,min δ 1,lt_min hδ zero_lt_one,?_⟩
  intro h hh₀ hhδ
  have hhδ' : h < δ := lt_of_lt_of_le hhδ (min_le_left _ _)
  have hh₁ : h < 1 := lt_of_lt_of_le hhδ (min_le_right _ _)
  exact hball (by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hh₀] using hhδ')
    (strict_radial_mem_injectivity hm (by linarith) (by linarith))

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
