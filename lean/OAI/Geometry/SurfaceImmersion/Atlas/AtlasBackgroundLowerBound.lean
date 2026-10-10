import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricLowerBound
import OAI.Geometry.SurfaceImmersion.Atlas.MetricReadBounds
import OAI.Geometry.SurfaceImmersion.Geometry.TensorPullbackNorm
import OAI.Geometry.SurfaceImmersion.Correction.GoodSmoothingAtlas

namespace OAI

/-! The fixed coordinate lower bound dominates any fixed smooth background
metric. Both constants are chosen before the finite preparation set. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma coordinateChart_differential (i : A.centers) {p : M}
    (hp : p ∈ (chart (i : M)).source) :
    mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart (i : M)) p =
      planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (surfaceDifferential (chart (i : M)) p) := by
  have he : (coordinateChart (i : M) : M → SmallModes.Base) =
      planeCoordinateIsometry ∘ (chart (i : M)) := rfl
  have hleft : MDifferentiable 𝓘(ℝ,Base) 𝓘(ℝ,SmallModes.Base) planeCoordinateIsometry :=
    (planeCoordinateIsometry.contDiff (n := (∞ : ℕ∞ω))).contMDiff.mdifferentiable (by simp)
  have hh := mfderiv_comp p hleft.mdifferentiableAt
    ((chart_mdifferentiable (i : M)).mdifferentiableAt hp)
  rw [mfderiv_eq_fderiv] at hh
  have hd : fderiv ℝ planeCoordinateIsometry (chart (i : M) p) =
      planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap :=
    planeCoordinateIsometry.toContinuousLinearEquiv.hasFDerivAt.fderiv
  rw [hd] at hh
  rw [he]
  exact hh

theorem uniform_background_metric_lower_bound (g : SmoothMetric M) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G → A.WeightedBound 1 1 δ (G-F) →
      ∀ (p : M) (v : TangentSpace planeModel p),
        c*g.inner p v v ≤ inducedForm G p v v := by
  obtain ⟨δ,a,hδ,ha,hlower⟩ := A.uniform_coordinate_metric_lower_bound hF hImm
  obtain ⟨T,B,_,_,_,hB,_,hbound,_⟩ := A.metric_plane_read_bounds g
  refine ⟨δ,a^2/(4*B+1),hδ,div_pos (sq_pos_of_pos ha) (by positivity),?_⟩
  intro G hG hclose p v
  obtain ⟨i,hi⟩ := A.mem_some_weightCore p
  have hp : p ∈ tsupport (A.weight i) := subset_tsupport _ (A.weightCore_nonzero i hi)
  let u := surfaceDifferential (chart (i : M)) p v
  have hmetric : g.inner p v v ≤ (4*B)*‖u‖^2 := by
    have hcoord : p ∈ (coordinateChart (i : M)).source := by
      simpa only [coordinateChart_source,chart_source] using A.weight_support i hp
    rw [← coordinateMetric_pullback_chart g (i : M) hcoord v v,
      ← A.tensorPlaneRead_metric_on_weight g i hp,A.coordinateChart_differential i (A.weight_support i hp)]
    change PhaseMean.evaluate _ (planeCoordinateIsometry u) (planeCoordinateIsometry u) ≤ _
    calc
      _ ≤ ‖PhaseMean.evaluate _ (planeCoordinateIsometry u) (planeCoordinateIsometry u)‖ := le_abs_self _
      _ ≤ 4*‖A.tensorPlaneRead i g.inner (planeCoordinateIsometry (chart (i : M) p))‖*
          ‖planeCoordinateIsometry u‖*‖planeCoordinateIsometry u‖ := PhaseMean.norm_evaluate_le _ _ _
      _ ≤ (4*B)*‖u‖^2 := by
        rw [planeCoordinateIsometry.norm_map]
        nlinarith [mul_nonneg (sub_nonneg.mpr (hbound i (planeCoordinateIsometry (chart (i : M) p))))
          (sq_nonneg ‖u‖)]
  have hL := hlower G hG hclose i (chart (i : M) p) (mem_image_of_mem _ hi) u
  have he : fderiv ℝ (A.vectorChartRead i G) (chart (i : M) p) u =
      surfaceDifferential G p v := by
    rw [A.vectorChartRead_differential i hG hp]
    rfl
  rw [he] at hL
  have hsq : a^2*‖u‖^2 ≤ ‖surfaceDifferential G p v‖^2 := by
    nlinarith [mul_nonneg ha.le (norm_nonneg u),norm_nonneg (surfaceDifferential G p v)]
  have hc : 0 ≤ a^2/(4*B+1) := by positivity
  have hcomp : a^2/(4*B+1)*g.inner p v v ≤ a^2*‖u‖^2 := by
    calc
      _ ≤ a^2/(4*B+1)*((4*B)*‖u‖^2) := mul_le_mul_of_nonneg_left hmetric hc
      _ = (a^2*((4*B)*‖u‖^2))/(4*B+1) := by ring
      _ ≤ a^2*‖u‖^2 := by
        apply (div_le_iff₀ (by positivity : 0 < 4*B+1)).2
        nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg ‖u‖)]
  exact hcomp.trans (by simpa only [inducedForm,real_inner_self_eq_norm_sq] using hsq)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
