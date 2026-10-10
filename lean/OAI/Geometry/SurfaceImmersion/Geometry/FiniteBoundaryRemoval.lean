import OAI.Geometry.SurfaceImmersion.Geometry.FiniteBoundaryStepGeometry

namespace OAI

/-! Removing the primitive's own boundary from the finite invariant. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {B : SmoothingAtlas M} {ι : Type*}

omit [CompactSpace M] in
lemma removed_boundary_crossings_subset (curves : ι → PhaseBoundaryCurve B) (a : ι) :
    boundaryCrossingSet (fun j : {j : ι // j ≠ a} => curves j) univ ⊆
      boundaryCrossingSet curves univ := by
  rintro p ⟨j,_,k,_,hjk,hj,hk⟩
  exact ⟨j,mem_univ _,k,mem_univ _,fun h => hjk (Subtype.ext h),hj,hk⟩

omit [CompactSpace M] in
lemma removed_boundary_crossings_disjoint (curves : ι → PhaseBoundaryCurve B) (a : ι)
    (htriple : ∀ j k l, j ≠ k → j ≠ l → k ≠ l →
      (curves j).carrier ∩ (curves k).carrier ∩ (curves l).carrier = ∅) :
    Disjoint (boundaryCrossingSet (fun j : {j : ι // j ≠ a} => curves j) univ)
      (curves a).carrier := by
  apply Set.disjoint_left.mpr
  rintro p ⟨j,_,k,_,hjk,hj,hk⟩ ha
  have hx : p ∈ (curves j).carrier ∩ (curves k).carrier ∩ (curves a).carrier := ⟨⟨hj,hk⟩,ha⟩
  rw [htriple j k a (fun h => hjk (Subtype.ext h)) j.2 k.2] at hx
  exact hx.elim

namespace FiniteBoundaryGeometry

lemma remove {curves : ι → PhaseBoundaryCurve B} {F : M → Space} {n : PreferredNormal F}
    (h : FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) F n) (a : ι) :
    FiniteBoundaryGeometry (fun j : {j : ι // j ≠ a} => curves j)
      (boundaryCrossingSet (fun j : {j : ι // j ≠ a} => curves j) univ) F n :=
  h.restrict Subtype.val Subtype.val_injective (removed_boundary_crossings_subset curves a)

lemma remove_frontier {curves : ι → PhaseBoundaryCurve B} {F : M → Space} {n : PreferredNormal F}
    (h : FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) F n) (a : ι) :
    ∀ (j : {j : ι // j ≠ a}) p, p ∈ (curves j).carrier ∩ (curves a).carrier →
      0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n.vector p) ∧
      0 < (curves a).crossing (curves j) F p := by
  intro j p hp
  have hE := boundaryCrossingSet_pair curves (mem_univ j.val) (mem_univ a) j.2 hp.1 hp.2
  exact ⟨h.positive j a j.2 p hE hp.1 hp.2,h.crossing a j j.2.symm p hE hp.2 hp.1⟩

end FiniteBoundaryGeometry
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
