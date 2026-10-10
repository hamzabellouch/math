import OAI.Analysis.CircleDomains.Uniformization.LabelledCoreIteration

namespace OAI

/-! Global representatives of the compact core correspondences. They
agree with the actual conformal maps throughout the open source. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {I:Type*} [Finite I]

def coreExtension {C D:FiniteJordanConfiguration I}
    (e:closure C.region ≃ₜ closure D.region) (p:Sphere) : Sphere := by
  classical
  exact if hp:p∈closure C.region then (e ⟨p,hp⟩:Sphere) else p

omit [Finite I] in
lemma coreExtension_eq {C D:FiniteJordanConfiguration I}
    (e:closure C.region ≃ₜ closure D.region) {p:Sphere} (hp:p∈closure C.region) :
    coreExtension e p=(e ⟨p,hp⟩:Sphere) := by simp only [coreExtension,dite_eq_left hp]

omit [Finite I] in
lemma coreExtension_continuousOn {C D:FiniteJordanConfiguration I}
    (e:closure C.region ≃ₜ closure D.region) :
    ContinuousOn (coreExtension e) (closure C.region) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (closure C.region).domRestrict (coreExtension e)=fun p => (e p:Sphere) := by
    funext p
    exact coreExtension_eq e p.property
  rw [he]
  exact continuous_subtype_val.comp e.continuous

omit [Finite I] in
lemma coreExtension_injOn {C D:FiniteJordanConfiguration I}
    (e:closure C.region ≃ₜ closure D.region) : InjOn (coreExtension e) (closure C.region) := by
  intro p hp q hq he
  rw [coreExtension_eq e hp,coreExtension_eq e hq] at he
  exact congrArg Subtype.val (e.injective (Subtype.val_injective he))

lemma exists_global_cumulative_core_extension (C:FiniteJordanConfiguration I)
    (ha:∀i,IsAnalyticJordanCap (C.hole i)) (schedule:ℕ→I) (n:ℕ) :
    ∃E:Sphere→Sphere, ContinuousOn E (closure C.region) ∧ InjOn E (closure C.region) ∧
      EqOn E (cumulativeMap C schedule n) C.region ∧
      E '' closure C.region=closure (iterate C schedule n).region ∧
      ∀i,E '' frontier (closedTerminalCap (C.hole i))=
        frontier (closedTerminalCap ((iterate C schedule n).hole i)) := by
  obtain ⟨e,he,hl⟩ := exists_cumulative_labelled_core_equiv C ha schedule n
  refine ⟨coreExtension e,coreExtension_continuousOn e,coreExtension_injOn e,?_,?_,?_⟩
  · intro p hp
    rw [coreExtension_eq e (subset_closure hp)]
    exact he _ hp
  · apply Subset.antisymm
    · rintro _ ⟨p,hp,rfl⟩
      rw [coreExtension_eq e hp]
      exact (e ⟨p,hp⟩).property
    · intro p hp
      obtain ⟨q,hq⟩ := e.surjective ⟨p,hp⟩
      refine ⟨q,q.property,?_⟩
      rw [coreExtension_eq e q.property]
      exact congrArg Subtype.val hq
  · intro i
    have hm : coreExtension e '' frontier (closedTerminalCap (C.hole i))=
        Subtype.val '' (e '' C.boundaryInCore i) := by
      apply Subset.antisymm
      · rintro _ ⟨p,hp,rfl⟩
        refine ⟨e ⟨p,C.boundary_subset_closure_region i hp⟩,
          ⟨⟨p,C.boundary_subset_closure_region i hp⟩,hp,rfl⟩,?_⟩
        exact (coreExtension_eq e (C.boundary_subset_closure_region i hp)).symm
      · rintro _ ⟨_,⟨q,hq,rfl⟩,rfl⟩
        exact ⟨q,hq,coreExtension_eq e q.property⟩
    rw [hm,hl i,(iterate C schedule n).boundaryInCore_image]

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
