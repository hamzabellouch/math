import OAI.Geometry.SurfaceImmersion.Primitive.TransverseCircularRadii
import OAI.Geometry.SurfaceImmersion.Primitive.GenericCircularPhases

namespace OAI

/-! The geometric finite preparation: independent radii and linear phase
parts are chosen before the starting immersion is flattened at the finite
crossing set. All statements concern the actual coordinate circles. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry PublishedInputs
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem finite_circular_preparation
    (index : ι → A.centers) (r0 lo hi L : ι → ℝ)
    (hlo : ∀ i, 0 < lo i) (hlohi : ∀ i, lo i < hi i) (hhi : ∀ i, hi i < r0 i)
    (hpos : ∀ i p, 0 < A.weight (index i) p ↔ p ∈ circularCoordinateDisk (index i : M) (r0 i))
    (hreg : ∀ i, circularCoordinateRegion (index i : M) (r0 i) ⊆
      (coordinateChart (index i : M)).target)
    (U : Set (ι → CurvePlane)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ (r : ι → ℝ) (ell : ι → CurvePlane), ell ∈ U ∧
      (∀ i, lo i < r i ∧ r i < hi i) ∧
      (circularCrossingSet (fun i => (index i : M)) r).Finite ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        circularBoundary (index i : M) (r i) ∩ circularBoundary (index j : M) (r j) ∩
          circularBoundary (index k : M) (r k) = ∅) ∧
      (∀ i j, i ≠ j → ∀ p ∈ circularBoundary (index i : M) (r i) ∩
          circularBoundary (index j : M) (r j),
        ∃ q : M, p ∈ (coordinateChart q).source ∧
          covectorDet (circularNormalCovector (index i : M) q p)
            (circularNormalCovector (index j : M) q p) ≠ 0) ∧
      (∀ i j, (circularPhaseTangencies (index i : M) (index j : M)
        (ell i) (L i) (r j) (r i)).Finite) ∧
      (∀ i j, i ≠ j → ∀ p ∈ circularCrossingSet (fun k => (index k : M)) r,
        p ∈ (coordinateChart (index i : M)).source →
        p ∈ (coordinateChart (index j : M)).source →
          covectorDet
            (phaseDerivative (centeredAtlasPhase (index i : M) (ell i) (L i) ∘
              (coordinateChart (index i : M)).symm) (coordinateChart (index i : M) p))
            (phaseDerivative (centeredAtlasPhase (index j : M) (ell j) (L j) ∘
              (coordinateChart (index i : M)).symm) (coordinateChart (index i : M) p)) ≠ 0) := by
  classical
  obtain ⟨r,hr,hpair,htriple,htrans⟩ := A.exists_transverse_circular_radii index r0 lo hi
    hlo hlohi hhi hpos
  let P : Set M := circularCrossingSet (fun i => (index i : M)) r
  have hP : P.Finite := circularCrossingSet_finite _ _ hpair
  let : Fintype P := hP.fintype
  let κ := {a : DistinctRadiusPairs ι × P //
    (a.2 : M) ∈ (coordinateChart (index a.1.1.1 : M)).source ∧
    (a.2 : M) ∈ (coordinateChart (index a.1.1.2 : M)).source}
  let : Fintype κ := Fintype.ofFinite κ
  let first : κ → ι := fun a => a.1.1.1.1
  let second : κ → ι := fun a => a.1.1.1.2
  let point : κ → M := fun a => a.1.2
  let base : κ → M := fun a => (index (first a) : M)
  have hrad (i : ι) : 0 < r i := (hlo i).trans (hr i).1
  have hnew (i : ι) : circularCoordinateRegion (index i : M) (r i) ⊆
      (coordinateChart (index i : M)).target := by
    have hs : (r i)^2 ≤ (r0 i)^2 := by
      have h1 := (hr i).2
      have h2 := hhi i
      have h3 := hrad i
      nlinarith
    intro x hx
    exact hreg i (hx.trans hs)
  obtain ⟨ell,hell,htangent,hcross⟩ := exists_generic_circular_phases
    (fun i => (index i : M)) L r hrad hnew first second (fun a => a.1.1.2)
    base point (fun a => a.2.1) (fun a => a.2.1) (fun a => a.2.2) U hU hne
  refine ⟨r,ell,hell,hr,hP,htriple,htrans,htangent,?_⟩
  intro i j hij p hp hi hj
  let a : κ := ⟨(⟨(i,j),hij⟩,⟨p,hp⟩),hi,hj⟩
  exact hcross a

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
