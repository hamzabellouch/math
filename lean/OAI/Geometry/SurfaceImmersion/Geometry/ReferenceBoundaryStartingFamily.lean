import OAI.Geometry.SurfaceImmersion.Geometry.ReferenceStartingFamily
import OAI.Geometry.SurfaceImmersion.Geometry.PreparedBoundaryStartingFamily
import OAI.Geometry.SurfaceImmersion.Primitive.CircularFamilyGeometry
import OAI.Geometry.SurfaceImmersion.Geometry.ScaledInitialMap
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseSphericalGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.PhasePreparedCrossings
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteBoundaryGeometry
import OAI.Geometry.SurfaceImmersion.Geometry.PositiveTensorMetric
import OAI.Geometry.SurfaceImmersion.Atlas.MetricGoodPhaseData

namespace OAI

/-! Reference and finite-point starting immersions with the same scale,
including the actual finite boundary invariant. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem reference_circular_starting_family (g : SmoothMetric M) {I : M → Space}
    (hI : ContMDiff planeModel spaceModel ∞ I) (hunit : ∀ p, ‖I p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel I p))
    {η : ℝ} (hη : 0 < η) :
    ∃ r D c : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ D ∧ 0 < c ∧
      A.WeightedBound 1 2 D I ∧
      A.TensorWeightedBound 1 1 η (inducedTensor (r • I)) ∧
      (∀ p v, inducedForm (r • I) p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
      ∀ (n : ℕ) (B : SmoothingAtlas M) (d : CircularFamilyGeometry B (Fin n))
        (ε : ℝ), 0 < ε →
      ∃ (G : M → Space) (g₀ : SmoothMetric M) (normal : PreferredNormal (r • G)),
        ContMDiff planeModel spaceModel ∞ G ∧ (∀ p, ‖G p‖ = 1) ∧
        IsSmoothIsometricImmersion M g₀ (r • G) ∧
        g₀.inner = inducedTensor (r • G) ∧ Nonempty (MetricGoodPhaseData g₀ (r • G)) ∧
        normal.vector = (fun p => -G p) ∧
        A.WeightedBound 1 1 ε (G-I) ∧ A.WeightedBound 1 2 D G ∧
        (∀ p v, c*g.inner p v v ≤ g₀.inner p v v) ∧
        A.TensorWeightedBound 1 1 η g₀.inner ∧
        (∀ p v, g₀.inner p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
        FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) (r • G) normal := by
  obtain ⟨r,D,c,hr,hr1,hD,hc,hIbound,hImetric,hIshort,hprep⟩ :=
    A.reference_small_metric_prepared_family g hI hunit hImm hη
  refine ⟨r,D,r^2*c,hr,hr1,hD,mul_pos (sq_pos_of_pos hr) hc,
    hIbound,hImetric,hIshort,?_⟩
  intro n B d ε hε
  let E := (boundaryCrossingSet_finite d.curves univ d.pair_finite).toFinset
  obtain ⟨a,G,normal,ha,hG,hu,hGI,hn,hclose,hbound,hlower,hmetric,hshort,hflat⟩ := hprep E ε hε
  have hbase (p : M) (v : Base) (hv : v ≠ 0) :=
    spherical_initial_boundary_geometry hG hu hr hGI p hv
  have hs : ContMDiff planeModel spaceModel ∞ (r • G) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hG
  let g₀ := A.immersionMetric hs hGI
  have hF : IsSmoothIsometricImmersion M g₀ (r • G) := ⟨hs,fun _ _ _ => rfl⟩
  have hdata : Nonempty (MetricGoodPhaseData g₀ (r • G)) :=
    MetricGoodPhaseData.nonempty g₀ hs hGI (fun p => ⟨dy,dy,
      (hbase p dy (by simp [dy])).2.1⟩)
  have hscaled (p : M) (v : TangentSpace planeModel p) :
      (r^2*c)*g.inner p v v ≤ g₀.inner p v v := by
    change (r^2*c)*g.inner p v v ≤ inducedTensor (r • G) p v v
    rw [inducedTensor_const_smul hG r]
    change (r^2*c)*g.inner p v v ≤ r^2*inducedForm G p v v
    calc
      _ = r^2*(c*g.inner p v v) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlower p v) (sq_nonneg r)
  refine ⟨G,g₀,normal,hG,hu,hF,rfl,hdata,hn,hclose,hbound,hscaled,hmetric,hshort,?_⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro j p hp
    exact ((d.curves j).spherical_second_positive hr hu hF hp).2.1
  · intro j p hp
    rw [hn]
    exact ((d.curves j).spherical_second_positive hr hu hF hp).2.2
  · intro j k _ p _ hp _
    rw [hn]
    exact ((d.curves j).spherical_second_positive hr hu hF hp).1
  · intro j k _ p hp hj hk
    apply (d.curves j).crossing_pos_of_coordinate_crossings (d.curves k) hF hj hk
    have hsource : p ∈ (coordinateChart ((d.curves j).index : M)).source := by
      rw [coordinateChart_source,← chart_source]
      exact ((d.curves j).source hj).1
    have hpE : p ∈ E := by simpa only [E,Set.Finite.mem_toFinset] using hp
    exact (A.prepared_point_crossings hG hu hr hGI (a ⟨p,hpE⟩)
      (ha ⟨p,hpE⟩) (hflat ⟨p,hpE⟩).2.2 ((d.curves j).index : M) hsource).2.2

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
