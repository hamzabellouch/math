import OAI.Geometry.SurfaceImmersion.Geometry.PreparedBoundaryStartingFamily
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseSphericalGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.PhasePreparedCrossings
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteBoundaryGeometry
import OAI.Geometry.SurfaceImmersion.Geometry.PositiveTensorMetric
import OAI.Geometry.SurfaceImmersion.Atlas.MetricGoodPhaseData

namespace OAI

/-! Uniform spherical starting immersions carrying all actual finite
boundary invariants. The scale and estimates precede the crossing set. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M) {ι : Type*} (curves : ι → PhaseBoundaryCurve B)

theorem finite_boundary_starting_family (g : SmoothMetric M) {I : M → Space}
    (hI : ContMDiff planeModel spaceModel ∞ I) (hunit : ∀ p, ‖I p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel I p))
    {η : ℝ} (hη : 0 < η) :
    ∃ r D c : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ D ∧ 0 < c ∧
      ∀ (E : Finset M) (ε : ℝ), 0 < ε →
      ∃ (G : M → Space) (g₀ : SmoothMetric M) (n : PreferredNormal (r • G)),
        ContMDiff planeModel spaceModel ∞ G ∧ (∀ p, ‖G p‖ = 1) ∧
        IsSmoothIsometricImmersion M g₀ (r • G) ∧
        g₀.inner = inducedTensor (r • G) ∧ Nonempty (MetricGoodPhaseData g₀ (r • G)) ∧
        n.vector = (fun p => -G p) ∧
        A.WeightedBound 1 1 ε (G-I) ∧ A.WeightedBound 1 2 D G ∧
        (∀ p v, c*g.inner p v v ≤ inducedForm G p v v) ∧
        A.TensorWeightedBound 1 1 η (inducedTensor (r • G)) ∧
        (∀ p v, inducedForm (r • G) p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
        FiniteBoundaryGeometry curves (E : Set M) (r • G) n := by
  obtain ⟨r,D,c,hr,hr1,hD,hc,hprep⟩ := A.small_metric_boundary_family g hI hunit hImm hη
  refine ⟨r,D,c,hr,hr1,hD,hc,?_⟩
  intro E ε hε
  obtain ⟨G,n,hG,hu,hGI,hn,hclose,hbound,hlower,hmetric,hshort,hbase,hcross⟩ := hprep E ε hε
  have hs : ContMDiff planeModel spaceModel ∞ (r • G) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hG
  let g₀ := A.immersionMetric hs hGI
  have hF : IsSmoothIsometricImmersion M g₀ (r • G) := ⟨hs,fun _ _ _ => rfl⟩
  have hdata : Nonempty (MetricGoodPhaseData g₀ (r • G)) :=
    MetricGoodPhaseData.nonempty g₀ hs hGI (fun p => ⟨dy,dy,
      (hbase p dy (by simp [dy])).2.1⟩)
  refine ⟨G,g₀,n,hG,hu,hF,rfl,hdata,hn,hclose,hbound,hlower,hmetric,hshort,?_⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro j p hp
    exact ((curves j).spherical_second_positive hr hu hF hp).2.1
  · intro j p hp
    rw [hn]
    exact ((curves j).spherical_second_positive hr hu hF hp).2.2
  · intro j k _ p _ hp _
    rw [hn]
    exact ((curves j).spherical_second_positive hr hu hF hp).1
  · intro j k _ p hp hj hk
    apply (curves j).crossing_pos_of_coordinate_crossings (curves k) hF hj hk
    have hsource : p ∈ (coordinateChart ((curves j).index : M)).source := by
      rw [coordinateChart_source,← chart_source]
      exact ((curves j).source hj).1
    exact ((hcross ⟨p,hp⟩).2 ((curves j).index : M) hsource).2

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
