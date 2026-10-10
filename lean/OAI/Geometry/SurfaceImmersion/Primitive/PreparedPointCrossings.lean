import OAI.Geometry.SurfaceImmersion.Atlas.PreparedPointCoordinates
import OAI.Geometry.SurfaceImmersion.Atlas.RadialFormCoordinateTransfer
import OAI.Geometry.SurfaceImmersion.Primitive.LocalIntrinsicCrossing

namespace OAI

/-! Initial crossing inequalities in every chart through a prepared point.
The curvature is the actual curvature of the scaled induced metric. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold Matrix
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes SphericalJets VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem prepared_point_crossings {G : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (hunit : ∀ p, ‖G p‖ = 1)
    {r : ℝ} (hr : 0 < r)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel (r • G) p))
    (i : A.centers) {p : M} (hp : A.weight i p ≠ 0)
    (hflat : ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (i : M)).symm)
      (chartAt Plane (i : M) p) v w = 0)
    (q : M) (hq : p ∈ (coordinateChart q).source) :
    (∀ v w, realSecondForm (coordinateMap (r • G) q) v w (coordinateChart q p) =
      (r⁻¹*(coordDeriv v (coordinateMap (r • G) q) (coordinateChart q p) ⬝ᵥ
        coordDeriv w (coordinateMap (r • G) q) (coordinateChart q p))) • spaceCoordinates (-G p)) ∧
    coordinateGaussianCurvature (realMetric (coordinateMap (r • G) q) dx dx)
      (realMetric (coordinateMap (r • G) q) dx dy)
      (realMetric (coordinateMap (r • G) q) dy dy) (coordinateChart q p) = (r⁻¹)^2 ∧
    ∀ v w : Base, v ≠ 0 → w ≠ 0 →
      0 < orderedCrossing (coordinateMap (r • G) q) v w (coordinateChart q p)
        (coordinateGaussianCurvature (realMetric (coordinateMap (r • G) q) dx dx)
          (realMetric (coordinateMap (r • G) q) dx dy)
          (realMetric (coordinateMap (r • G) q) dy dy) (coordinateChart q p)) := by
  have hs : ContMDiff planeModel spaceModel ∞ (r • G) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hG
  have hi : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support i (subset_tsupport _ hp)
  have hdi := coordinateMap_injective_of_immersion hs hI (i : M)
    (by rw [← coordinateChart_target]; exact (coordinateChart (i : M)).map_source hi)
  have hrad := A.prepared_point_radial_form hG hr.ne' hI i hp hflat
  have hB := radial_form_coordinate_transfer hs (i : M) q p hi hq
    (gramDet_ne_zero_of_injective _ hdi) (spaceCoordinates (-G p)) r hrad
  have hdom : coordinateChart q p ∈ coordinateDomain q := by
    rw [← coordinateChart_target]
    exact (coordinateChart q).map_source hq
  have hImm := coordinateMap_injective_of_immersion hs hI q hdom
  have hD := gramDet_ne_zero_of_injective _ hImm
  have hn : spaceCoordinates (-G p) ⬝ᵥ spaceCoordinates (-G p) = 1 := by
    rw [spaceCoordinates_dot,real_inner_self_eq_norm_sq,norm_neg,hunit]
    norm_num
  refine ⟨hB,coordinateGaussianCurvature_pure_radial_on (coordinateDomain_open q)
    (coordinateMap_smoothOn hs q) hdom _ hn hD hB,?_⟩
  intro v w hv hw
  apply orderedCrossing_intrinsic_pure_radial_on (coordinateDomain_open q)
    (coordinateMap_smoothOn hs q) hdom v w _ hr hn hD hB
  · intro hz
    exact hv (hImm (by simpa only [coordDeriv,map_zero] using hz))
  · intro hz
    exact hw (hImm (by simpa only [coordDeriv,map_zero] using hz))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
