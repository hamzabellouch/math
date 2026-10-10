import OAI.Analysis.CircleDomains.Uniformization.LabelledCoreCorrespondence

namespace OAI

/-! The actual compact core maps preserve every boundary label under
finite composition. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {I:Type*} [Finite I]

def boundaryInCore (C:FiniteJordanConfiguration I) (i:I) : Set (closure C.region) :=
  {p | (p:Sphere)∈frontier (closedTerminalCap (C.hole i))}

lemma boundaryInCore_image (C:FiniteJordanConfiguration I) (i:I) :
    Subtype.val '' C.boundaryInCore i=frontier (closedTerminalCap (C.hole i)) := by
  apply Subset.antisymm
  · rintro _ ⟨p,hp,rfl⟩
    exact hp
  · intro p hp
    exact ⟨⟨p,C.boundary_subset_closure_region i hp⟩,hp,rfl⟩

lemma Step.exists_labelled_core_equiv {C:FiniteJordanConfiguration I} {j:I}
    (q:Step C j) (ha:IsAnalyticJordanCap (C.hole j)) :
    ∃e : closure C.region ≃ₜ closure q.target.region,
      (∀p : closure C.region, (p:Sphere)∈C.region → (e p:Sphere)=q.map p) ∧
      ∀i,e '' C.boundaryInCore i=q.target.boundaryInCore i := by
  obtain ⟨e,he,hl⟩ := q.exists_labelled_core_correspondence ha
  refine ⟨e,he,?_⟩
  intro i
  apply Subtype.val_injective.image_injective
  rw [image_image,q.target.boundaryInCore_image]
  exact hl i

lemma exists_cumulative_labelled_core_equiv (C:FiniteJordanConfiguration I)
    (ha:∀i,IsAnalyticJordanCap (C.hole i)) (schedule:ℕ→I) (n:ℕ) :
    ∃e : closure C.region ≃ₜ closure (iterate C schedule n).region,
      (∀p : closure C.region, (p:Sphere)∈C.region →
        (e p:Sphere)=cumulativeMap C schedule n p) ∧
      ∀i,e '' C.boundaryInCore i=(iterate C schedule n).boundaryInCore i := by
  induction n with
  | zero =>
    refine ⟨Homeomorph.refl _,fun _ _ => rfl,?_⟩
    intro i
    exact image_id _
  | succ n ih =>
    obtain ⟨e,he,hl⟩ := ih
    let q := chosenStep (iterate C schedule n) (schedule n)
    obtain ⟨d,hd,hdlabel⟩ := q.exists_labelled_core_equiv
      (iterate_analytic_of_initial C ha schedule n (schedule n))
    refine ⟨e.trans d,?_,?_⟩
    · intro p hp
      have hep : (e p:Sphere)∈(iterate C schedule n).region := by
        rw [he p hp]
        exact (cumulativeMap_conformal C schedule n).bijOn.mapsTo hp
      change (d (e p):Sphere)=stageMap C schedule n (cumulativeMap C schedule n p)
      rw [hd (e p) hep,he p hp]
      rfl
    · intro i
      change (d ∘ e) '' C.boundaryInCore i=q.target.boundaryInCore i
      rw [image_comp,hl i,hdlabel i]

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
