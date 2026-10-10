import OAI.Geometry.SurfaceImmersion.Geometry.EuclideanRestoration
import OAI.Geometry.SurfaceImmersion.Atlas.VectorChartRead

namespace OAI

/-! Smooth Euclidean representatives agree with the actual chart map near
points where a partition weight is nonzero. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def euclideanChartRead (i : A.centers) (F : M → Space) : Plane → Space :=
  A.vectorChartRead i F ∘ EuclideanSpace.equiv (Fin 2) ℝ

lemma euclideanChartRead_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ContDiff ℝ ∞ (A.euclideanChartRead i F) :=
  (A.vectorChartRead_smooth i hF).comp (EuclideanSpace.equiv (Fin 2) ℝ).contDiff

omit [CompactSpace M] in
lemma euclideanChartRead_eq (i : A.centers) (F : M → Space) :
    A.euclideanChartRead i F = (chartAt Plane (i : M)).target.indicator
      (fun x => (A.outer i ((chartAt Plane (i : M)).symm x))^2 •
        F ((chartAt Plane (i : M)).symm x)) := by
  funext x
  by_cases hx : x ∈ (chartAt Plane (i : M)).target
  · simp [euclideanChartRead,vectorChartRead,localize,chart,hx]
    rfl
  · simp [euclideanChartRead,vectorChartRead,localize,chart,hx]

omit [CompactSpace M] in
lemma outer_one_chart_germ (i : A.centers) {p : M} (hp : A.weight i p ≠ 0) :
    (fun y => A.outer i ((chartAt Plane (i : M)).symm y)) =ᶠ[𝓝 (chartAt Plane (i : M) p)]
      (fun _ => (1 : ℝ)) := by
  have hps : p ∈ (chartAt Plane (i : M)).source := by
    simpa only [chart_source] using A.weight_support i (subset_tsupport _ hp)
  have hpt := (chartAt Plane (i : M)).map_source hps
  have hc : ContinuousAt (fun y => A.weight i ((chartAt Plane (i : M)).symm y))
      (chartAt Plane (i : M) p) :=
    (A.weight_smooth i).continuous.continuousAt.comp
      (((chartAt Plane (i : M)).continuousOn_symm _ hpt).continuousAt
        ((chartAt Plane (i : M)).open_target.mem_nhds hpt))
  have hn : ∀ᶠ y in 𝓝 (chartAt Plane (i : M) p),
      A.weight i ((chartAt Plane (i : M)).symm y) ≠ 0 :=
    hc.eventually_ne (by simpa only [(chartAt Plane (i : M)).left_inv hps] using hp)
  exact hn.mono fun y hy => A.outer_one i _ (subset_tsupport _ hy)

omit [CompactSpace M] in
lemma euclideanChartRead_germ (i : A.centers) (F : M → Space) {p : M}
    (hp : A.weight i p ≠ 0) :
    A.euclideanChartRead i F =ᶠ[𝓝 (chartAt Plane (i : M) p)]
      F ∘ (chartAt Plane (i : M)).symm := by
  have hps : p ∈ (chartAt Plane (i : M)).source := by
    simpa only [chart_source] using A.weight_support i (subset_tsupport _ hp)
  filter_upwards [(chartAt Plane (i : M)).open_target.mem_nhds
    ((chartAt Plane (i : M)).map_source hps),A.outer_one_chart_germ i hp] with y hy ho
  rw [A.euclideanChartRead_eq,indicator_of_mem hy,ho,one_pow,one_smul]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
