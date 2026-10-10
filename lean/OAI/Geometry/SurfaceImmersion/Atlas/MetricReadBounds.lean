import OAI.Geometry.SurfaceImmersion.Atlas.MetricAtlasReference
import OAI.Geometry.Immersion.ClosedSurface.MetricBounds
import OAI.Geometry.SurfaceImmersion.Geometry.CompactSectionBounds

namespace OAI

/-! Compact positive metric range and global first-order bounds for atlas readings. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes WeightedEstimates
local instance metricReadBoundsFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance metricReadBoundsFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance metricReadBoundsDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricReadBoundsDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricReadBoundsSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReadBoundsSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma metricReadSupport_domain (i : A.centers) :
    (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coordinateDomain (i : M) := by
  rintro x ⟨y,⟨p,hp,rfl⟩,rfl⟩
  have hs : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support i hp
  rw [← coordinateChart_target]
  exact (coordinateChart (i : M)).map_source hs

theorem metric_plane_read_bounds (g : SmoothMetric M) :
    ∃ T : Set PhaseMean.Tensor, ∃ B : ℝ, IsCompact T ∧
      (∀ H ∈ T, 0 < H 0) ∧ (∀ H ∈ T, 0 < H 0*H 2-(H 1)^2) ∧ 1 ≤ B ∧
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        A.tensorPlaneRead i g.inner x ∈ T) ∧
      (∀ i x, ‖A.tensorPlaneRead i g.inner x‖ ≤ B) ∧
      (∀ i x y, ‖A.tensorPlaneRead i g.inner y-A.tensorPlaneRead i g.inner x‖ ≤ B*‖y-x‖) := by
  classical
  let T : Set PhaseMean.Tensor := ⋃ i : A.centers,
    A.tensorPlaneRead i g.inner '' (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)
  have hT : IsCompact T := isCompact_iUnion (fun i =>
    (modeSupport (A.chartWeightCompact i)).isCompact.image (A.tensorPlaneRead_metric_smooth g i).continuous)
  have hpos (H : PhaseMean.Tensor) (hH : H ∈ T) :
      0 < H 0 ∧ 0 < H 0*H 2-(H 1)^2 := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hH
    rw [A.tensorPlaneRead_metric g i hx]
    exact coordinateMetric_positive g (i : M) (A.metricReadSupport_domain i hx)
  obtain ⟨C,hC,hbound⟩ := A.exists_bundle_bound A.tensorTriv A.tensorTriv_domain 1 g.contMDiff
  choose D hD hd using fun i : A.centers => A.tensorPlaneRead_bound i 1
  let B : ℝ := 1+∑ i : A.centers, D i*C
  have hB : 1 ≤ B := by
    have hh := Finset.sum_nonneg (s := Finset.univ) (fun i _ => mul_nonneg (hD i) hC)
    change 1 ≤ 1+∑ i : A.centers, D i*C
    linarith
  have hb (i : A.centers) : WeightedEstimates.WeightedBound univ 1 1 B (A.tensorPlaneRead i g.inner) := by
    apply (hd i g.inner 1 C zero_lt_one le_rfl hC g.contMDiff hbound).mono_const
    have hh := Finset.single_le_sum (s := Finset.univ)
      (fun i _ => mul_nonneg (hD i) hC) (Finset.mem_univ i)
    change D i*C ≤ 1+∑ i : A.centers, D i*C
    linarith
  refine ⟨T,B,hT,fun H hH => (hpos H hH).1,fun H hH => (hpos H hH).2,hB,
    fun i x hx => mem_iUnion.mpr ⟨i,mem_image_of_mem _ hx⟩,
    fun i x => (hb i).norm_le (mem_univ x),?_⟩
  intro i x y
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) _ _
    (convex_univ : Convex ℝ (univ : Set SmallModes.Base)) (mem_univ x) (mem_univ y)
  · intro a _
    exact (A.tensorPlaneRead_metric_smooth g i).differentiable (by simp) a
  · intro a _
    have hh := (hb i).deriv_le zero_lt_one (le_refl 1) (mem_univ a)
    simpa only [iteratedFDerivWithin_univ,one_pow,div_one,norm_iteratedFDeriv_one] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
