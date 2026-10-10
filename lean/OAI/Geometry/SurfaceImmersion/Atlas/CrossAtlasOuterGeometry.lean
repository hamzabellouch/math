import OAI.Geometry.SurfaceImmersion.Atlas.PhaseOuterImmersion
import OAI.Geometry.SurfaceImmersion.Primitive.IntrinsicCrossingNaturality

namespace OAI

/-! The old and new analytic atlases represent the same immersion on a
common outer plateau, including all second forms and intrinsic crossings. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

lemma phase_germ_of_common_outer (i : A.centers) (j : B.centers)
    (hc : (i : M) = (j : M))
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : Base} (hx : x ∈ (surfacePhaseChart (j : M) e).target)
    (ho : A.outer i =ᶠ[𝓝 ((surfacePhaseChart (j : M) e).symm x)] (fun _ => 1))
    (hw : B.weight j ((surfacePhaseChart (j : M) e).symm x) ≠ 0) :
    A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x] B.phaseRealChartMap j e.symm F := by
  have hxA : x ∈ (surfacePhaseChart (i : M) e).target := by rwa [hc]
  have hoA : A.outer i =ᶠ[𝓝 ((surfacePhaseChart (i : M) e).symm x)] (fun _ => 1) := by rwa [hc]
  have hA := A.phaseRealChartMap_surface_germ_of_outer i e F hxA hoA
  have hB := B.phaseRealChartMap_surface_germ j e F hx hw
  rw [hc] at hA
  exact hA.trans hB.symm

lemma phase_second_of_common_outer (i : A.centers) (j : B.centers)
    (hc : (i : M) = (j : M))
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : Base} (hx : x ∈ (surfacePhaseChart (j : M) e).target)
    (ho : A.outer i =ᶠ[𝓝 ((surfacePhaseChart (j : M) e).symm x)] (fun _ => 1))
    (hw : B.weight j ((surfacePhaseChart (j : M) e).symm x) ≠ 0) (v w : Base) :
    realSecondForm (A.phaseRealChartMap i e.symm F) v w x =
      realSecondForm (B.phaseRealChartMap j e.symm F) v w x :=
  (realSecondForm_eventuallyEq (A.phase_germ_of_common_outer B i j hc e F hx ho hw) v w).eq_of_nhds

lemma phase_crossing_of_common_outer (i : A.centers) (j : B.centers)
    (hc : (i : M) = (j : M))
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : Base} (hx : x ∈ (surfacePhaseChart (j : M) e).target)
    (ho : A.outer i =ᶠ[𝓝 ((surfacePhaseChart (j : M) e).symm x)] (fun _ => 1))
    (hw : B.weight j ((surfacePhaseChart (j : M) e).symm x) ≠ 0) (v w : Base) :
    orderedCrossing (A.phaseRealChartMap i e.symm F) v w x
        (coordinateGaussianCurvature (realMetric (A.phaseRealChartMap i e.symm F) dx dx)
          (realMetric (A.phaseRealChartMap i e.symm F) dx dy)
          (realMetric (A.phaseRealChartMap i e.symm F) dy dy) x) =
      orderedCrossing (B.phaseRealChartMap j e.symm F) v w x
        (coordinateGaussianCurvature (realMetric (B.phaseRealChartMap j e.symm F) dx dx)
          (realMetric (B.phaseRealChartMap j e.symm F) dx dy)
          (realMetric (B.phaseRealChartMap j e.symm F) dy dy) x) :=
  orderedCrossing_intrinsic_germ (A.phase_germ_of_common_outer B i j hc e F hx ho hw) v w

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
