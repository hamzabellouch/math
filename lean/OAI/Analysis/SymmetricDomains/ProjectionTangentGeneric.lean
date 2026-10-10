import Mathlib
import OAI.Analysis.SymmetricDomains.OldOffsetOldPosition

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical

theorem coordinate_rank_ge_of_chart_generic {d m N : ℕ}
    (q : (Fin d → ℝ) → Affine N) {x : Fin d → ℝ}
    (J : Affine N → Affine m) (hJ : AnalyticAt ℂ J (q x))
    (hq : DifferentiableAt ℝ q x)
    (hgen : Submodule.span ℂ (range (fderiv ℝ (J ∘ q) x)) = ⊤) :
    m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) := by
  let M := (fderiv ℂ J (q x)).toLinearMap
  let S := Submodule.span ℂ (range (fderiv ℝ q x))
  have hd : fderiv ℝ (J ∘ q) x = ((fderiv ℂ J (q x)).restrictScalars ℝ).comp (fderiv ℝ q x) :=
    ((hJ.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x hq.hasFDerivAt).fderiv
  have hmap : S.map M = ⊤ := by
    dsimp only [S]
    rw [Submodule.map_span]
    have he : M '' range (fderiv ℝ q x) = range (fderiv ℝ (J ∘ q) x) := by
      rw [← range_comp,hd]
      rfl
    rw [he,hgen]
  rw [coordinate_derivative_rank q hq]
  have hh := Submodule.finrank_map_le M S
  rw [hmap] at hh
  simpa only [finrank_top,Affine,Module.finrank_pi,Fintype.card_fin,S] using hh

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

theorem projection_inverse_germ (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) :
    (fun y => c.chart.inverse (c.chart.projection (q y-q c.center))) =ᶠ[𝓝 x] q := by
  have hs := c.normal.parameters.open_source.mem_nhds hgood.1
  have hb := (c.normal.parameters.continuousAt hgood.1).preimage_mem_nhds
    (isOpen_ball.mem_nhds hgood.2.1)
  have h0 : c.chart.projection (q c.center-q c.center) = 0 := by rw [sub_self,map_zero]
  filter_upwards [hs,hb] with y hy hyb
  have hgr := c.normal.graph_identity (c.normal.parameters y) (ball_subset_ball c.graphRadius_le hyb)
  simp only [c.normal.parameters.left_inv hy,h0,sub_zero] at hgr
  have hpos : c.oldPosition (c.normal.parameters y) = c.chart.projection (q y-q c.center) := by
    apply c.normal.realCoordinates.injective
    rw [oldPosition,ContinuousLinearEquiv.apply_symm_apply]
    exact hgr.symm
  rw [← hpos]
  simpa only [oldPosition,c.normal.parameters.left_inv hy] using (c.graph_boundary _ hyb).2.2

theorem projection_tangent_generic (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) (hq : DifferentiableAt ℝ q x)
    (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Function.Injective (fderiv ℝ (fun y => c.chart.projection (q y-q c.center)) x) ∧
    Submodule.span ℂ (range (fderiv ℝ (fun y => c.chart.projection (q y-q c.center)) x)) = ⊤ := by
  let a := c.oldPosition (c.normal.parameters x)
  let F := fun z => c.chart.inverse (z+a)
  let G := fun y => c.chart.projection (y-q c.center)-a
  have ha : ‖complexRealEquiv m a‖ < c.chart.radius := (c.graph_boundary _ hgood.2.1).2.1
  have hF0 : F 0 = q x := by simpa only [F,zero_add] using c.oldPosition_inverse hgood
  have hF : AnalyticAt ℂ F 0 := by
    have hfa : AnalyticAt ℂ c.chart.inverse ((0 : Affine m)+a) := by
      simpa only [zero_add] using c.chart.inverse_analytic a ha
    exact hfa.comp (f := fun z : Affine m => z+a) (x := 0) (analyticAt_id.add analyticAt_const)
  have hG : AnalyticAt ℂ G (q x) :=
    ((c.chart.projection.analyticAt _).comp (analyticAt_id.sub analyticAt_const)).sub analyticAt_const
  have hT : IsOpen {z : Affine m | ‖complexRealEquiv m (z+a)‖ < c.chart.radius} :=
    isOpen_lt (((complexRealEquiv m).continuous.comp (continuous_id.add continuous_const)).norm) continuous_const
  have hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id := by
    filter_upwards [hT.mem_nhds (by simpa using ha)] with z hz
    change c.chart.projection (c.chart.inverse (z+a)-q c.center)-a = z
    rw [c.chart.left_inverse (z+a) hz,add_sub_cancel_right]
  have hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q := by
    simpa only [F,G,Function.comp_def,sub_add_cancel] using c.projection_inverse_germ hgood
  have ht := chart_parametric_generic F G q hF0 hF hG hq hqi hGF hFG hr
  have hd : fderiv ℝ (G ∘ q) x = fderiv ℝ (fun y => c.chart.projection (q y-q c.center)) x := by
    have hh := (((c.chart.projection.restrictScalars ℝ).differentiableAt.comp x
      (hq.sub_const (q c.center))).hasFDerivAt.sub_const a).fderiv
    exact hh
  rwa [hd] at ht
end NashBoundaryChart
end Release061

end

end OAI
