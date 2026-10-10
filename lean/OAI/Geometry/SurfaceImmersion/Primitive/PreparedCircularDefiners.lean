import OAI.Geometry.SurfaceImmersion.Primitive.CircularPhaseLocalDefiner
import OAI.Geometry.SurfaceImmersion.Primitive.TransverseCircularRadii

namespace OAI

/-! Generic circle crossings and phase tangencies give exactly the finite
exception set used by the supported angular-loop construction. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {ι : Type*} [Fintype ι]

lemma prepared_circular_definers (q : M) (center : ι → M) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i)
    (hreg : ∀ i, circularCoordinateRegion (center i) (r i) ⊆ (coordinateChart (center i)).target)
    (ell : Base) (L R : ℝ)
    (hpair : (circularCrossingSet center r).Finite)
    (htang : ∀ i, (circularPhaseTangencies q (center i) ell L (r i) R).Finite)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hdom : e.source ⊆ (coordinateChart q).target)
    (hphase : ∀ x, (e x).1 = centeredConvexPhase ell L (coordinateChart q q) x)
    {K : Set Base} (hK : K ⊆ e.target)
    (hcover : ∀ x ∈ K, ∃ i, (coordinateChart q).symm (e.symm x) ∈ circularBoundary (center i) (r i))
    (hregion : ∀ x ∈ K, (coordinateChart q).symm (e.symm x) ∈ circularDiskClosure q R) :
    ∃ P : Set Base, P.Finite ∧ P ⊆ K ∧
      ∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
        ∃ g : Base → ℝ, ContDiffOn ℝ ∞ g N ∧ (∀ x ∈ K ∩ N, g x = 0) ∧
          fderiv ℝ g p dy ≠ 0 := by
  let m : Base → M := fun x => (coordinateChart q).symm (e.symm x)
  let B : Set M := circularCrossingSet center r ∪
    ⋃ i, circularPhaseTangencies q (center i) ell L (r i) R
  have hB : B.Finite := hpair.union (Set.finite_iUnion htang)
  let P : Set Base := K ∩ (fun z : M => e (coordinateChart q z)) '' B
  have hP : P.Finite := (hB.image _).subset inter_subset_right
  have hinverse (x : Base) (hx : x ∈ K) : e (coordinateChart q (m x)) = x := by
    dsimp only [m]
    rw [(coordinateChart q).right_inv (hdom (e.map_target (hK hx))),e.right_inv (hK hx)]
  have hnot (x : Base) (hx : x ∈ K \ P) : m x ∉ B := by
    intro hb
    exact hx.2 ⟨hx.1,⟨m x,hb,hinverse x hx.1⟩⟩
  refine ⟨P,hP,inter_subset_left,?_⟩
  apply finite_boundary_local_definers (fun i => circularBoundary (center i) (r i))
    (fun i => (circularBoundary_compact (center i) (hr i) (hreg i)).isClosed) m
  · intro x hx
    exact ((coordinateChart_symm_smoothOn q).contMDiffAt
      ((coordinateChart q).open_target.mem_nhds (hdom (e.map_target (hK hx))))).continuousAt.comp
      (hi.continuous.continuousAt)
  · exact hcover
  · intro i j hij x hx hxi hxj
    refine ⟨hx,⟨m x,Or.inl ?_,hinverse x hx⟩⟩
    exact mem_iUnion.mpr ⟨⟨(i,j),hij⟩,⟨hxi,hxj⟩⟩
  · intro i x hx hxi
    apply circular_boundary_phase_definer q (center i) ell L (r i) e he hi hdom hphase (hK hx.1) hxi
    intro hz
    apply hnot x hx
    exact Or.inr (mem_iUnion.mpr ⟨i,⟨⟨hxi,hregion x hx.1⟩,hz⟩⟩)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
