import Mathlib

namespace OAI

section
noncomputable section
open Set Function Topology

namespace CriticalPercolation.ConnectedAction
variable {A X : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
variable [TopologicalSpace X] [DiscreteTopology X]

lemma open_kernel [LocallyConnectedSpace A] (ρ : A →* Equiv.Perm X)
    (hcont : ∀ x, Continuous (fun a => ρ a x)) :
    IsOpen (ρ.ker : Set A) := by
  have hsub : connectedComponent (1 : A) ⊆ (ρ.ker : Set A) := by
    intro g hg
    apply Equiv.ext
    intro x
    have hh := ((isPreconnected_connectedComponent (x := (1 : A))).image
      (fun a => ρ a x) (hcont x).continuousOn).subsingleton
    have he := hh ⟨g,hg,rfl⟩ ⟨1,mem_connectedComponent,rfl⟩
    simpa only [map_one,Equiv.Perm.one_apply] using he
  exact ρ.ker.isOpen_of_mem_nhds (g := 1)
    (Filter.mem_of_superset (isOpen_connectedComponent.mem_nhds mem_connectedComponent) hsub)

lemma open_kernel_of_locallyConnected_quotient
    (ρ : A →* Equiv.Perm X) (hcont : ∀ x, Continuous (fun a => ρ a x))
    (H : Subgroup A) [H.Normal] (hH : H≤ρ.ker)
    [LocallyConnectedSpace (A ⧸ H)] :
    IsOpen (ρ.ker : Set A) := by
  let ψ := QuotientGroup.lift H ρ hH
  have hψ : ∀ x, Continuous (fun q => ψ q x) := by
    intro x
    apply (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr
    exact hcont x
  have ho := open_kernel ψ hψ
  exact ho.preimage QuotientGroup.continuous_mk

lemma open_kernel_of_open_locallyConnected_subquotient
    (ρ : A →* Equiv.Perm X) (hcont : ∀ x, Continuous (fun a => ρ a x))
    (L H : Subgroup A) [H.Normal] (hL : IsOpen (L : Set A)) (hH : H≤ρ.ker)
    [LocallyConnectedSpace (L ⧸ H.subgroupOf L)] :
    IsOpen (ρ.ker : Set A) := by
  have hsub : H.subgroupOf L≤(ρ.comp L.subtype).ker := by
    intro a ha
    exact hH ha
  have ho := open_kernel_of_locallyConnected_quotient (ρ.comp L.subtype)
    (fun x => (hcont x).comp continuous_subtype_val) (H.subgroupOf L) hsub
  have him : IsOpen ((Subtype.val : L → A) ''
      (((ρ.comp L.subtype).ker : Subgroup L) : Set L)) :=
    hL.isOpenMap_subtype_val _ ho
  apply ρ.ker.isOpen_of_mem_nhds (g := 1)
  apply Filter.mem_of_superset (him.mem_nhds ?_) ?_
  · exact ⟨1,(ρ.comp L.subtype).ker.one_mem,rfl⟩
  · rintro a ⟨a,ha,rfl⟩
    exact ha

end CriticalPercolation.ConnectedAction
end
end

end OAI
