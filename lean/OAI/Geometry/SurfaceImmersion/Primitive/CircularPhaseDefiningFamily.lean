import OAI.Geometry.SurfaceImmersion.Primitive.CircularPhaseLocalDefiner
import OAI.Geometry.SurfaceImmersion.Primitive.CircularDiskTopology

namespace OAI

/-! The finite exceptional tangencies of actual coordinate circles supply
all local defining functions required by the supported angular loop. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {ι : Type*} [Fintype ι]

theorem circular_phase_defining_family (q : M) (ell : Base) (L R : ℝ)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hdom : e.source ⊆ (coordinateChart q).target)
    (hphase : ∀ x, (e x).1 = centeredConvexPhase ell L (coordinateChart q q) x)
    (hQ : circularCoordinateRegion q R ⊆ (coordinateChart q).target)
    (hcover : circularDiskClosure q R ⊆ ((coordinateChart q).trans e).source)
    (center : ι → M) (r : ι → ℝ) (hr : ∀ j, 0 < r j)
    (hreg : ∀ j, circularCoordinateRegion (center j) (r j) ⊆ (coordinateChart (center j)).target)
    (E₀ : Set M) (hE₀ : E₀.Finite)
    (hcross : ∀ j k, j ≠ k → circularBoundary (center j) (r j) ∩ circularBoundary (center k) (r k) ⊆ E₀)
    (htan : ∀ j, (circularPhaseTangencies q (center j) ell L (r j) R).Finite) :
    let E := (coordinateChart q).trans e
    let Curves := fun j => E '' (circularBoundary (center j) (r j) ∩ circularDiskClosure q R)
    (∀ j, IsCompact (Curves j)) ∧ ∃ P : Set Base, P.Finite ∧
      ∀ p ∈ (⋃ j, Curves j) \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
        ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f N ∧
          (∀ x ∈ (⋃ j, Curves j) ∩ N, f x = 0) ∧ fderiv ℝ f p dy ≠ 0 := by
  classical
  let E := (coordinateChart q).trans e
  let C := fun j => circularBoundary (center j) (r j)
  let S := circularDiskClosure q R
  let Curves := fun j => E '' (C j ∩ S)
  let Z := E₀ ∪ ⋃ j, circularPhaseTangencies q (center j) ell L (r j) R
  let P := E '' Z
  have hZ : Z.Finite := hE₀.union (Set.finite_iUnion htan)
  have hP : P.Finite := hZ.image E
  have hS : IsCompact S := circularDiskClosure_compact q R hQ
  have hC (j : ι) : IsCompact (C j) := circularBoundary_compact (center j) (hr j) (hreg j)
  have hcompact (j : ι) : IsCompact (Curves j) :=
    ((hC j).inter hS).image_of_continuousOn (E.continuousOn.mono (fun _ hp => hcover hp.2))
  have hback {x : Base} (hx : x ∈ ⋃ j, Curves j) : x ∈ E.target ∧ E.symm x ∈ S := by
    obtain ⟨j,y,hy,rfl⟩ := mem_iUnion.mp hx
    exact ⟨E.map_source (hcover hy.2),by rw [E.left_inv (hcover hy.2)]; exact hy.2⟩
  have hpoint {j : ι} {x : Base} (hx : x ∈ Curves j) : E.symm x ∈ C j := by
    obtain ⟨y,hy,rfl⟩ := hx
    rw [E.left_inv (hcover hy.2)]
    exact hy.1
  refine ⟨hcompact,P,hP,?_⟩
  apply finite_boundary_local_definers C (fun j => (hC j).isClosed) E.symm
  · intro p hp
    exact E.continuousAt_symm (hback hp).1
  · intro p hp
    obtain ⟨j,hj⟩ := mem_iUnion.mp hp
    exact ⟨j,hpoint hj⟩
  · intro j k hjk p hp hpj hpk
    have hz : E.symm p ∈ Z := Or.inl (hcross j k hjk ⟨hpj,hpk⟩)
    exact ⟨E.symm p,hz,E.right_inv (hback hp).1⟩
  · intro j p hp hpj
    have hpE : p ∈ E.target := (hback hp.1).1
    have hpT : p ∈ e.target := hpE.1
    have hnt : circularPhaseDerivative q (center j) ell L (E.symm p) ≠ 0 := by
      intro hz
      apply hp.2
      refine ⟨E.symm p,Or.inr (mem_iUnion.mpr ⟨j,?_⟩),E.right_inv hpE⟩
      exact ⟨⟨hpj,(hback hp.1).2⟩,hz⟩
    exact circular_boundary_phase_definer q (center j) ell L (r j) e he hi hdom hphase
      hpT hpj hnt

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
