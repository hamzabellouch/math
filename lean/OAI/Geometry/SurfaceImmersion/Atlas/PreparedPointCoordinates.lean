import OAI.Geometry.SurfaceImmersion.Atlas.FixedAtlasStartingFamily
import OAI.Geometry.SurfaceImmersion.Geometry.PreparedRadialSecondForm
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasImmersionGeometry

namespace OAI

/-! A prepared spherical point has the exact radial second form in its
selected atlas chart, using a genuine smooth representative of the chart map. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold Matrix
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem prepared_point_radial_form {G : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) {r : ℝ} (hr : r ≠ 0)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel (r • G) p))
    (i : A.centers) {p : M} (hp : A.weight i p ≠ 0)
    (hflat : ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (i : M)).symm)
      (chartAt Plane (i : M) p) v w = 0) (v w : SmallModes.Base) :
    realSecondForm (coordinateMap (r • G) (i : M)) v w (coordinateChart (i : M) p) =
      (r⁻¹*(coordDeriv v (coordinateMap (r • G) (i : M)) (coordinateChart (i : M) p) ⬝ᵥ
        coordDeriv w (coordinateMap (r • G) (i : M)) (coordinateChart (i : M) p))) •
          spaceCoordinates (-G p) := by
  let F := A.euclideanChartRead i G
  let x := coordinateChart (i : M) p
  have hx : planeCoordinates.symm x = chartAt Plane (i : M) p := by
    simp [x,coordinateChart_apply,chartCoordinates]
  have he := A.euclideanChartRead_germ i G hp
  have hf : ContDiff ℝ ∞ F := A.euclideanChartRead_smooth i hG
  have hflatF : ∀ a b, sphericalSecondForm F (planeCoordinates.symm x) a b = 0 := by
    intro a b
    rw [hx]
    exact (sphericalSecondForm_congr_germ he a b).trans (hflat a b)
  have hs : scaledSphereCoordinates F r =ᶠ[𝓝 x] coordinateMap (r • G) (i : M) := by
    have ht : Tendsto planeCoordinates.symm (𝓝 x) (𝓝 (chartAt Plane (i : M) p)) := by
      rw [← hx]
      exact planeCoordinates.symm.continuous.continuousAt.tendsto
    filter_upwards [he.comp_tendsto ht] with y hy
    simp only [scaledSphereCoordinates,coordinateMap,Function.comp_apply,Pi.smul_apply]
    change F (planeCoordinates.symm y) = _ at hy
    dsimp only [F]
    dsimp only [F] at hy
    rw [hy]
    rfl
  have hscaled : ContMDiff planeModel spaceModel ∞ (r • G) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hG
  have hps : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support i (subset_tsupport _ hp)
  have hD := gramDet_ne_zero_of_injective _
    (coordinateMap_injective_of_immersion hscaled hI (i : M)
      (by rw [← coordinateChart_target]; exact (coordinateChart (i : M)).map_source hps))
  have hD' : NormalFrame.gramDet (coordDeriv dx (scaledSphereCoordinates F r) x)
      (coordDeriv dy (scaledSphereCoordinates F r) x) ≠ 0 := by
    rw [(coordDeriv_eventuallyEq hs dx).eq_of_nhds,(coordDeriv_eventuallyEq hs dy).eq_of_nhds]
    exact hD
  have hvalue : F (planeCoordinates.symm x) = G p := by
    dsimp only [F]
    rw [hx,he.eq_of_nhds]
    exact congrArg G ((chartAt Plane (i : M)).left_inv (by simpa only [coordinateChart_source] using hps))
  have hh := scaled_flat_spherical_secondForm hf hr x hflatF hD' v w
  rw [(realSecondForm_eventuallyEq hs v w).eq_of_nhds,
    (coordDeriv_eventuallyEq hs v).eq_of_nhds,
    (coordDeriv_eventuallyEq hs w).eq_of_nhds,hvalue] at hh
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
