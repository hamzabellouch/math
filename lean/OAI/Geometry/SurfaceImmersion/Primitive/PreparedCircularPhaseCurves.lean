import OAI.Geometry.SurfaceImmersion.Primitive.UniformCircularPhaseCharts
import OAI.Geometry.SurfaceImmersion.Primitive.FiniteCircularPreparation

namespace OAI

/-! Actual fixed phase-curve families after generic radius and phase
selection. The admissible chart radii are fixed before either selection. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SurfaceJetCoordinates SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem prepared_circular_phase_curves (P : ι → Set Base)
    (hP : ∀ i, IsCompact (P i)) (hP0 : ∀ i ell, ell ∈ P i → ell ≠ 0)
    (L : ι → ℝ) (hL : ∀ i, 0 < L i) :
    ∃ R : ι → ℝ, (∀ i, 0 < R i) ∧
      ∀ (index : ι → A.centers) (r₀ lo hi : ι → ℝ),
      (∀ i, 0 < lo i) → (∀ i, lo i < hi i) → (∀ i, hi i < r₀ i) →
      (∀ i, r₀ i ≤ R i) →
      (∀ i p, 0 < A.weight (index i) p ↔ p ∈ circularCoordinateDisk (index i : M) (r₀ i)) →
      (∀ i, circularCoordinateRegion (index i : M) (r₀ i) ⊆ (coordinateChart (index i : M)).target) →
      ∀ U : Set (ι → Base), IsOpen U → U.Nonempty → (∀ ell ∈ U, ∀ i, ell i ∈ P i) →
      ∃ (r : ι → ℝ) (ell : ι → Base) (curves : ι → PhaseBoundaryCurve A),
        ell ∈ U ∧ (∀ i, lo i < r i ∧ r i < hi i) ∧
        (∀ i, (curves i).index = index i) ∧
        (∀ i, (curves i).carrier = circularBoundary (index i : M) (r i)) ∧
        (∀ i x, (baseEquiv ((curves i).phase x)).1 =
          centeredConvexPhase (ell i) (L i) (coordinateChart (index i : M) (index i)) (baseEquiv x)) ∧
        (∀ i x, x ∈ circularCoordinateRegion (index i : M) (r i) →
          baseEquiv.symm x ∈ (curves i).phase.source) ∧
        (circularCrossingSet (fun i => (index i : M)) r).Finite ∧
        (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
          (curves i).carrier ∩ (curves j).carrier ∩ (curves k).carrier = ∅) ∧
        (∀ i j, i ≠ j → ∀ p ∈ (curves i).carrier ∩ (curves j).carrier,
          ∃ q : M, p ∈ (coordinateChart q).source ∧
            covectorDet (circularNormalCovector (index i : M) q p)
              (circularNormalCovector (index j : M) q p) ≠ 0) ∧
        (∀ i j, (circularPhaseTangencies (index i : M) (index j : M)
          (ell i) (L i) (r j) (r i)).Finite) ∧
        (∀ i j, i ≠ j → ∀ p ∈ circularCrossingSet (fun k => (index k : M)) r,
          p ∈ (coordinateChart (index i : M)).source → p ∈ (coordinateChart (index j : M)).source →
            covectorDet
              (phaseDerivative (centeredAtlasPhase (index i : M) (ell i) (L i) ∘
                (coordinateChart (index i : M)).symm) (coordinateChart (index i : M) p))
              (phaseDerivative (centeredAtlasPhase (index j : M) (ell j) (L j) ∘
                (coordinateChart (index i : M)).symm) (coordinateChart (index i : M) p)) ≠ 0) := by
  choose R hR hcharts using fun i => uniform_circular_phase_charts (M := M) (hP i) (hP0 i) (hL i)
  refine ⟨R,hR,?_⟩
  intro index r₀ lo hi hlo hlohi hhi hrR hpos hreg U hU hne hUP
  obtain ⟨r,ell,hell,hr,hcross,htriple,htrans,htangent,hind⟩ :=
    A.finite_circular_preparation index r₀ lo hi L hlo hlohi hhi hpos hreg U hU hne
  have hrpos (i : ι) : 0 < r i := (hlo i).trans (hr i).1
  have hr0 (i : ι) : r i < r₀ i := (hr i).2.trans (hhi i)
  have hrreg (i : ι) : circularCoordinateRegion (index i : M) (r i) ⊆
      (coordinateChart (index i : M)).target := by
    intro x hx
    apply hreg i
    change circularRadiusSquared (coordinateChart (index i : M) (index i)) x ≤ (r i)^2 at hx
    change circularRadiusSquared (coordinateChart (index i : M) (index i)) x ≤ (r₀ i)^2
    exact hx.trans (by nlinarith [hrpos i,hr0 i])
  choose e he hei hephase hecover using fun i => hcharts i (index i) (ell i) (hUP ell hell i)
  have hcover (i : ι) : ∀ x ∈ circularCoordinateRegion (index i : M) (r i),
      baseEquiv.symm x ∈ (e i).source :=
    hecover i (r i) (hrpos i).le ((hr0 i).le.trans (hrR i))
  let curves : ι → PhaseBoundaryCurve A := fun i =>
    A.circularPhaseBoundaryCurve (index i) (hrpos i) (by nlinarith [hrpos i,hr0 i])
      (hpos i) (hrreg i) (e i) (he i) (hei i) (hcover i)
  refine ⟨r,ell,curves,hell,hr,(fun _ => rfl),(fun _ => rfl),hephase,hcover,
    hcross,htriple,htrans,htangent,hind⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
