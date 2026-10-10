import OAI.Analysis.CircleDomains.Uniformization.CircularizationBoundaryImages

namespace OAI

/-! The compact correspondence keeps the actual labels of all finite
boundary curves, including the newly circularized one. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {I:Type*} [Finite I]

lemma boundary_subset_closure_region (C:FiniteJordanConfiguration I) (i:I) :
    frontier (closedTerminalCap (C.hole i))⊆closure C.region := by
  have hc : IsClosed (closedJordanCore C.hole) :=
    (isOpen_iUnion fun j => OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen (C.hole j))).isClosed_compl
  have he : closure C.region=closedJordanCore C.hole := by
    change closure (openCompletedRegion C.hole)=_
    rw [←interior_closedJordanCore]
    exact closure_interior_closedJordanCore C.hole C.disjoint
  rw [he]
  intro p hp
  have hpf : p∈frontier (closedJordanCore C.hole) := by
    rw [frontier_closedJordanCore C.hole C.disjoint]
    exact mem_iUnion.mpr ⟨i,frontier_closedTerminalCap (C.hole i) ▸ hp⟩
  exact hc.closure_eq ▸ frontier_subset_closure hpf

lemma Step.exists_labelled_core_correspondence {C:FiniteJordanConfiguration I} {j:I}
    (q:Step C j) (ha:IsAnalyticJordanCap (C.hole j)) :
    ∃e : closure C.region ≃ₜ closure q.target.region,
      (∀p : closure C.region, (p:Sphere)∈C.region → (e p:Sphere)=q.map p) ∧
      ∀i, (fun p : closure C.region => (e p:Sphere)) ''
        {p | (p:Sphere)∈frontier (closedTerminalCap (C.hole i))}=
          frontier (closedTerminalCap (q.target.hole i)) := by
  obtain ⟨e,hE,he⟩ := q.exists_core_correspondence_exact ha
  refine ⟨e,he,?_⟩
  intro i
  let U := (closedTerminalCap (C.hole j))ᶜ
  let T := exteriorDiskNormalization q.center q.radius q.radius_pos
  let E := T.symm ∘ extendFrom U (T ∘ q.map)
  have him : (fun p : closure C.region => E p) ''
      {p | (p:Sphere)∈frontier (closedTerminalCap (C.hole i))}=
      E '' frontier (closedTerminalCap (C.hole i)) := by
    apply Subset.antisymm
    · rintro _ ⟨p,hp,rfl⟩
      exact ⟨p,hp,rfl⟩
    · rintro _ ⟨p,hp,rfl⟩
      exact ⟨⟨p,C.boundary_subset_closure_region i hp⟩,hp,rfl⟩
  calc
    _ = (fun p : closure C.region => E p) ''
        {p | (p:Sphere)∈frontier (closedTerminalCap (C.hole i))} :=
      image_congr (fun p _ => hE p)
    _ = E '' frontier (closedTerminalCap (C.hole i)) := him
    _ = _ := q.extended_boundary_images ha i

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
