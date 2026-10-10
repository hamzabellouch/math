import OAI.Geometry.SurfaceImmersion.Primitive.CircularFamilyGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.ShrinkingCircularWeight

namespace OAI

/-! The actual independent radius cutoffs for the selected circular geometry. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace CircularFamilyGeometry
variable {A : SmoothingAtlas M} (q : CircularFamilyGeometry A (A.centers × Fin 3))

def shrinkingWeights (a : A.centers × Fin 3) : M → ℝ :=
  shrinkingCircularWeight (a.1 : M) (A.weight a.1) (q.outerRadius a) (q.radius a)

omit [CompactSpace M] in
 theorem shrinkingWeights_data (hindex : ∀ a, (q.curves a).index = a.1)
    (hregion : ∀ a, circularCoordinateRegion (a.1 : M) (q.outerRadius a) ⊆
      (coordinateChart (a.1 : M)).target)
    (hw : ∀ i p, 0 ≤ A.weight i p) :
    (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (q.shrinkingWeights a)) ∧
    (∀ a p, 0 ≤ q.shrinkingWeights a p) ∧
    (∀ a p, 0 < q.shrinkingWeights a p ↔
      p ∈ circularCoordinateDisk ((q.curves a).index : M) (q.radius a)) ∧
    (∀ a, tsupport (q.shrinkingWeights a) ⊆ (chart (a.1 : M)).source) := by
  have hs (a : A.centers × Fin 3) := shrinkingCircularWeight_smooth (a.1 : M) (A.weight a.1)
    (A.weight_smooth a.1) (hregion a) (q.radius_outer a)
  refine ⟨fun a => (hs a).1,?_,?_,?_⟩
  · intro a p
    exact (shrinkingCircularWeight_nonneg_le (a.1 : M) (A.weight a.1) (hw a.1)
      (q.radius_outer a).le p).1
  · intro a p
    rw [hindex a]
    apply shrinkingCircularWeight_pos_iff (a.1 : M) (A.weight a.1) (hw a.1) (q.radius_outer a).le
    intro x
    simpa only [hindex] using q.weight_positive a x
  · intro a p hp
    have hr : circularCoordinateRegion (a.1 : M) (q.radius a) ⊆
        (coordinateChart (a.1 : M)).target := by simpa only [hindex] using q.region a
    have hsp := circularDiskClosure_source (a.1 : M) (q.radius a) hr ((hs a).2 hp)
    rwa [coordinateChart_source,← chart_source] at hsp

end CircularFamilyGeometry
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
