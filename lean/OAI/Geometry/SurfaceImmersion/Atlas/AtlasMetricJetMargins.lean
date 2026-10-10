import OAI.Geometry.SurfaceImmersion.Geometry.MetricJetMargins
import OAI.Geometry.SurfaceImmersion.Correction.AtlasMetricLocalModel
import OAI.Geometry.SurfaceImmersion.Atlas.MetricAtlasReference
import OAI.Geometry.SurfaceImmersion.Atlas.UniformMetricPhaseGeometry

namespace OAI

/-! Uniform first-jet geometry of approximate isometries in a fixed atlas. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry JetPolynomial JetPolynomial.Perturbation
local instance metricJetsFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricJetsFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance metricJetsDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricJetsDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricJetsSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricJetsSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma modeSupport_subset_coordinateDomain (i : A.centers) :
    (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coordinateDomain (i : M) := by
  rintro x ⟨y,⟨p,hp,rfl⟩,rfl⟩
  have hs : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support i hp
  rw [← coordinateChart_target]
  exact (coordinateChart (i : M)).map_source hs

lemma metricPlaneRead_on_support {V : M → Space}
    (hV : ContMDiff planeModel spaceModel ∞ V) (i : A.centers) {x : SmallModes.Base}
    (hx : x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i V) x =
      A.tensorPlaneRead i (inducedTensor V) x := by
  obtain ⟨y,hy,rfl⟩ := hx
  rw [← A.jetChartMap_plane]
  simpa only [tensorPlaneRead,Function.comp_apply,LinearIsometryEquiv.symm_apply_apply] using
    A.metric_read_on_support i hV hy

/-- The constants depend on the prescribed metric and fixed atlas, not on
any derivatives of the approximate immersion. -/
theorem metric_firstJet_margin (g : SmoothMetric M) :
    ∃ ε R c : ℝ, 0 < ε ∧ 0 < R ∧ 0 < c ∧
      ∀ V : M → Space, ContMDiff planeModel spaceModel ∞ V →
      ∀ b : ℝ, 0 ≤ b → b < ε →
      A.TensorWeightedBound 1 0 b (inducedTensor V-g.inner) →
      ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i V) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i V) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i V) x).2 := by
  let T : Set PhaseMean.Tensor := ⋃ i : A.centers,
    A.tensorPlaneRead i g.inner '' (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)
  have hT : IsCompact T := isCompact_iUnion (fun i =>
    (modeSupport (A.chartWeightCompact i)).isCompact.image (A.tensorPlaneRead_smooth i g.contMDiff).continuous)
  have hpos : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2 := by
    intro H hH
    obtain ⟨i,hi⟩ := mem_iUnion.mp hH
    obtain ⟨x,hx,rfl⟩ := hi
    rw [A.tensorPlaneRead_metric g i hx]
    exact (coordinateMetric_positive g (i : M) (A.modeSupport_subset_coordinateDomain i hx)).2
  obtain ⟨ε,R,c,hε,hR,hc,hmargin⟩ := compact_metric_firstJet_margin hT hpos
  choose D hD hread using fun i : A.centers => A.tensorPlaneRead_bound i 0
  have heps (i : A.centers) : 0 < ε/(1+D i) := div_pos hε (by linarith [hD i])
  obtain ⟨ρ,hρ,_,hρall⟩ := finite_positive_threshold (fun i => ε/(1+D i)) heps
  refine ⟨ρ,R,c,hρ,hR,hc,?_⟩
  intro V hV b hb hbρ hclose i x hx
  apply hmargin (spaceCoordinates ∘ A.vectorPlaneRead i V) x (A.tensorPlaneRead i g.inner x)
    (mem_iUnion.mpr ⟨i,mem_image_of_mem _ hx⟩)
  have hlocal := hread i (inducedTensor V-g.inner) 1 b zero_lt_one le_rfl hb
    ((A.inducedTensor_smooth hV).sub_section g.contMDiff) hclose
  have hh := hlocal.norm_le (mem_univ x)
  rw [A.tensorPlaneRead_sub] at hh
  rw [A.metricPlaneRead_on_support hV i hx]
  have hb' := (lt_div_iff₀ (by linarith [hD i] : 0 < 1+D i)).mp
    (hbρ.trans_le (hρall i))
  exact hh.trans_lt (by nlinarith)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
