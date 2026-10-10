import OAI.Geometry.SurfaceImmersion.Primitive.GenericCircularRadii
import OAI.Geometry.SurfaceImmersion.Primitive.CircularRadiusCovectors

namespace OAI

/-! Generic radii give transverse actual coordinate circles, not merely
regular levels of their auxiliary global extensions. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry PublishedInputs
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exists_transverse_circular_radii
    (index : ι → A.centers) (r0 lo hi : ι → ℝ)
    (hlo : ∀ i, 0 < lo i) (hlohi : ∀ i, lo i < hi i) (hhi : ∀ i, hi i < r0 i)
    (hpos : ∀ i p, 0 < A.weight (index i) p ↔ p ∈ circularCoordinateDisk (index i : M) (r0 i)) :
    ∃ r : ι → ℝ, (∀ i, lo i < r i ∧ r i < hi i) ∧
      (∀ i j, i ≠ j → (circularBoundary (index i : M) (r i) ∩
        circularBoundary (index j : M) (r j)).Finite) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        circularBoundary (index i : M) (r i) ∩ circularBoundary (index j : M) (r j) ∩
          circularBoundary (index k : M) (r k) = ∅) ∧
      (∀ i j, i ≠ j → ∀ p ∈ circularBoundary (index i : M) (r i) ∩
          circularBoundary (index j : M) (r j),
        ∃ q : M, p ∈ (coordinateChart q).source ∧
          covectorDet (circularNormalCovector (index i : M) q p)
            (circularNormalCovector (index j : M) q p) ≠ 0) := by
  obtain ⟨r,hr,hfinite,htriple,hregular⟩ :=
    A.exists_generic_circular_radii index r0 lo hi hlo hlohi hhi hpos
  have hsmall (i : ι) : (r i)^2 < (r0 i)^2 := by
    have h1 := hlo i
    have h2 := hr i
    have h3 := hhi i
    nlinarith
  refine ⟨r,hr,hfinite,htriple,?_⟩
  intro i j hij p hp
  obtain ⟨q,hq,hreg⟩ := hregular i j hij p hp
  exact ⟨q,by simpa only [coordinateChart_source] using hq,
    A.actual_circular_normals_independent index r r0 i j hsmall hpos hp hq hreg⟩

end SmoothingAtlas

def circularCrossingSet (center : ι → M) (r : ι → ℝ) : Set M :=
  ⋃ a : DistinctRadiusPairs ι, circularBoundary (center a.1.1) (r a.1.1) ∩
    circularBoundary (center a.1.2) (r a.1.2)

omit [IsManifold planeModel ∞ M] [CompactSpace M] [DecidableEq ι] in
lemma circularCrossingSet_finite (center : ι → M) (r : ι → ℝ)
    (hfinite : ∀ i j, i ≠ j → (circularBoundary (center i) (r i) ∩
      circularBoundary (center j) (r j)).Finite) : (circularCrossingSet center r).Finite :=
  Set.finite_iUnion (fun a => hfinite a.1.1 a.1.2 a.2)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
