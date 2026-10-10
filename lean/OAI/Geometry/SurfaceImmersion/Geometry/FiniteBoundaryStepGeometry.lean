import OAI.Geometry.SurfaceImmersion.Primitive.FiniteBoundaryCrossingSets

namespace OAI

/-! The finite invariant supplies precisely the old boundary inequalities
and the crossing set disjointness required at the next primitive step. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

lemma finite_boundary_step_geometry (curves : ι → PhaseBoundaryCurve B)
    {s : Set ι} {a : ι} (ha : a ∉ s)
    (hpair : ∀ i j, i ≠ j → ((curves i).carrier ∩ (curves j).carrier).Finite)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (curves i).carrier ∩ (curves j).carrier ∩ (curves k).carrier = ∅)
    {F : M → Space} {n : PreferredNormal F}
    (h : FiniteBoundaryGeometry curves (boundaryCrossingSet curves (insert a s)) F n) :
    (boundaryCrossingSet curves s).Finite ∧
    Disjoint (boundaryCrossingSet curves s) (curves a).carrier ∧
    (∀ p ∈ (curves a).carrier,
      realSecondForm (B.phaseRealChartMap (curves a).index (curves a).phase.symm F)
        dy dy ((curves a).coordinate p) ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize
        (realSecondForm (B.phaseRealChartMap (curves a).index (curves a).phase.symm F)
          dy dy ((curves a).coordinate p))) ∧
    ∀ j ∈ s, ∀ p ∈ (curves j).carrier ∩ (curves a).carrier,
      0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n.vector p) ∧
      0 < (curves a).crossing (curves j) F p ∧ 0 < (curves j).crossing (curves a) F p := by
  refine ⟨boundaryCrossingSet_finite curves s hpair,
    boundaryCrossingSet_disjoint_next curves ha htriple,?_,?_⟩
  · intro p hp
    rw [← (curves a).second_eq F hp]
    exact ⟨h.nonzero a p hp,h.avoids a p hp⟩
  · intro j hj p hp
    have hja : j ≠ a := fun he => ha (he ▸ hj)
    have hE : p ∈ boundaryCrossingSet curves (insert a s) :=
      boundaryCrossingSet_pair curves (mem_insert_of_mem _ hj) (mem_insert _ _) hja hp.1 hp.2
    exact ⟨h.positive j a hja p hE hp.1 hp.2,
      h.crossing a j hja.symm p hE hp.2 hp.1,h.crossing j a hja p hE hp.1 hp.2⟩

omit [CompactSpace M] [Fintype ι] in
/-- At a listed crossing exactly two remaining curves occur. The point
itself indexes the crossing, so no duplicate crossing labels are introduced. -/
lemma boundaryCrossingSet_select (curves : ι → PhaseBoundaryCurve B) (s : Set ι)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (curves i).carrier ∩ (curves j).carrier ∩ (curves k).carrier = ∅) :
    ∃ left right : boundaryCrossingSet curves s → ι,
      (∀ p, left p ∈ s ∧ right p ∈ s ∧ left p ≠ right p ∧
        (p : M) ∈ (curves (left p)).carrier ∧ (p : M) ∈ (curves (right p)).carrier) ∧
      ∀ (p : boundaryCrossingSet curves s) j, (p : M) ∈ (curves j).carrier → j = left p ∨ j = right p := by
  classical
  have hex (p : boundaryCrossingSet curves s) :
      ∃ i j, i ∈ s ∧ j ∈ s ∧ i ≠ j ∧
        (p : M) ∈ (curves i).carrier ∧ (p : M) ∈ (curves j).carrier := by
    obtain ⟨i,hi,j,hj,hij,hpi,hpj⟩ := p.2
    exact ⟨i,j,hi,hj,hij,hpi,hpj⟩
  choose left right hchoice using hex
  refine ⟨left,right,hchoice,?_⟩
  intro p j hpj
  by_cases hl : j = left p
  · exact Or.inl hl
  by_cases hr : j = right p
  · exact Or.inr hr
  have hh := hchoice p
  have hx : (p : M) ∈ (curves (left p)).carrier ∩ (curves (right p)).carrier ∩ (curves j).carrier :=
    ⟨⟨hh.2.2.2.1,hh.2.2.2.2⟩,hpj⟩
  rw [htriple (left p) (right p) j hh.2.2.1 (Ne.symm hl) (Ne.symm hr)] at hx
  exact hx.elim

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
