import OAI.Geometry.SurfaceImmersion.Geometry.FiniteBoundaryGeometry

namespace OAI

/-! Exact crossing sets for the remaining curves in a finite induction.
The no-three-curves condition keeps these points off the next boundary. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

noncomputable def boundaryCrossingSet (curves : ι → PhaseBoundaryCurve B) (s : Set ι) : Set M :=
  {p | ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ p ∈ (curves i).carrier ∧ p ∈ (curves j).carrier}

omit [CompactSpace M] in
lemma boundaryCrossingSet_finite (curves : ι → PhaseBoundaryCurve B) (s : Set ι)
    (hpair : ∀ i j, i ≠ j → ((curves i).carrier ∩ (curves j).carrier).Finite) :
    (boundaryCrossingSet curves s).Finite := by
  classical
  have hU : (⋃ a : {a : ι × ι // a.1 ≠ a.2},
      (curves a.1.1).carrier ∩ (curves a.1.2).carrier).Finite :=
    Set.finite_iUnion (fun a => hpair a.1.1 a.1.2 a.2)
  apply hU.subset
  rintro p ⟨i,_,j,_,hij,hi,hj⟩
  exact mem_iUnion.mpr ⟨⟨(i,j),hij⟩,hi,hj⟩

omit [CompactSpace M] [Fintype ι] in
lemma boundaryCrossingSet_mono (curves : ι → PhaseBoundaryCurve B)
    {s t : Set ι} (hst : s ⊆ t) : boundaryCrossingSet curves s ⊆ boundaryCrossingSet curves t := by
  rintro p ⟨i,hi,j,hj,hij,hpi,hpj⟩
  exact ⟨i,hst hi,j,hst hj,hij,hpi,hpj⟩

omit [CompactSpace M] [Fintype ι] in
lemma boundaryCrossingSet_pair (curves : ι → PhaseBoundaryCurve B) {s : Set ι}
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) {p : M}
    (hpi : p ∈ (curves i).carrier) (hpj : p ∈ (curves j).carrier) :
    p ∈ boundaryCrossingSet curves s := ⟨i,hi,j,hj,hij,hpi,hpj⟩

omit [CompactSpace M] [Fintype ι] in
lemma boundaryCrossingSet_disjoint_next (curves : ι → PhaseBoundaryCurve B)
    {s : Set ι} {a : ι} (ha : a ∉ s)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (curves i).carrier ∩ (curves j).carrier ∩ (curves k).carrier = ∅) :
    Disjoint (boundaryCrossingSet curves s) (curves a).carrier := by
  apply Set.disjoint_left.mpr
  rintro p ⟨i,hi,j,hj,hij,hpi,hpj⟩ hpa
  have hia : i ≠ a := fun he => ha (he ▸ hi)
  have hja : j ≠ a := fun he => ha (he ▸ hj)
  have hx : p ∈ (curves i).carrier ∩ (curves j).carrier ∩ (curves a).carrier := ⟨⟨hpi,hpj⟩,hpa⟩
  rw [htriple i j a hij hia hja] at hx
  exact hx

omit [Fintype ι] in
lemma finiteBoundaryGeometry_restrict_remaining {curves : ι → PhaseBoundaryCurve B}
    {t : Set ι} {F : M → Space} {n : PreferredNormal F}
    (h : FiniteBoundaryGeometry curves (boundaryCrossingSet curves t) F n)
    {s : Set ι} (hst : s ⊆ t) :
    FiniteBoundaryGeometry (fun i : s => curves i)
      (boundaryCrossingSet curves s) F n := by
  exact h.restrict Subtype.val Subtype.val_injective (boundaryCrossingSet_mono curves hst)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
