import OAI.Geometry.SurfaceImmersion.Primitive.PreparedPointCrossings
import OAI.Geometry.SurfaceImmersion.Geometry.SphericalInitialBoundary

namespace OAI

/-! The uniform initial family with the actual crossing geometry needed by
the finite primitive induction. Its constants precede the finite crossing set. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold Matrix
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes SphericalJets VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem small_metric_boundary_family (g : SmoothMetric M) {I : M → Space}
    (hI : ContMDiff planeModel spaceModel ∞ I) (hunit : ∀ p, ‖I p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel I p))
    {η : ℝ} (hη : 0 < η) :
    ∃ r D c : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ D ∧ 0 < c ∧
      ∀ (P : Finset M) (ε : ℝ), 0 < ε →
      ∃ (G : M → Space) (n : PreferredNormal (r • G)),
        ContMDiff planeModel spaceModel ∞ G ∧ (∀ p, ‖G p‖ = 1) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel (r • G) p)) ∧
        n.vector = (fun p => -G p) ∧
        A.WeightedBound 1 1 ε (G-I) ∧ A.WeightedBound 1 2 D G ∧
        (∀ p v, c*g.inner p v v ≤ inducedForm G p v v) ∧
        A.TensorWeightedBound 1 1 η (inducedTensor (r • G)) ∧
        (∀ p v, inducedForm (r • G) p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
        (∀ p (v : Base), v ≠ 0 →
          0 < realSecondForm (coordinateMap (r • G) p) v v (coordinateCenter p) ⬝ᵥ
            spaceCoordinates (n.vector p) ∧
          realSecondForm (coordinateMap (r • G) p) v v (coordinateCenter p) ≠ 0 ∧
          normalize (realSecondForm (coordinateMap (r • G) p) v v (coordinateCenter p)) ≠
            -spaceCoordinates (n.vector p)) ∧
        ∀ p : P, G p = I p ∧ ∀ q : M, (p : M) ∈ (coordinateChart q).source →
          coordinateGaussianCurvature (realMetric (coordinateMap (r • G) q) dx dx)
            (realMetric (coordinateMap (r • G) q) dx dy)
            (realMetric (coordinateMap (r • G) q) dy dy) (coordinateChart q p) = (r⁻¹)^2 ∧
          ∀ v w : Base, v ≠ 0 → w ≠ 0 →
            0 < orderedCrossing (coordinateMap (r • G) q) v w (coordinateChart q p)
              (coordinateGaussianCurvature (realMetric (coordinateMap (r • G) q) dx dx)
                (realMetric (coordinateMap (r • G) q) dx dy)
                (realMetric (coordinateMap (r • G) q) dy dy) (coordinateChart q p)) := by
  obtain ⟨r,D,c,hr,hr1,hD,hc,hprep⟩ := A.small_metric_prepared_family g hI hunit hImm hη
  refine ⟨r,D,c,hr,hr1,hD,hc,?_⟩
  intro P ε hε
  obtain ⟨a,G,n,ha,hG,hu,hGI,hn,hclose,hbound,hlower,hmetric,hshort,hflat⟩ := hprep P ε hε
  refine ⟨G,n,hG,hu,hGI,hn,hclose,hbound,hlower,hmetric,hshort,?_,?_⟩
  · intro p v hv
    rw [hn]
    exact spherical_initial_boundary_geometry hG hu hr hGI p hv
  · intro p
    refine ⟨(hflat p).1,?_⟩
    intro q hq
    exact (A.prepared_point_crossings hG hu hr hGI (a p) (ha p) (hflat p).2.2 q hq).2

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
