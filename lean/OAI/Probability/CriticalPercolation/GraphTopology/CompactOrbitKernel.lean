import Mathlib
import OAI.Probability.CriticalPercolation.GraphTopology.GraphNeighborhoodCompact
import OAI.Probability.CriticalPercolation.GraphGeometry.NormalOrbitAction
import OAI.Probability.CriticalPercolation.GraphGeometry.LocallyConnectedActionKernel

namespace OAI

section
noncomputable section
open Set Function Topology
open scoped Classical

namespace CriticalPercolation.GraphTopology
variable {X : Type*} (Γ : SimpleGraph X)

def orbitKernel (H : Subgroup (Γ ≃g Γ)) [H.Normal] : Subgroup (Γ ≃g Γ) :=
  (NormalOrbit.blockHom (X := X) H).ker

instance orbitKernel_normal (H : Subgroup (Γ ≃g Γ)) [H.Normal] :
    (orbitKernel Γ H).Normal := MonoidHom.normal_ker _

lemma mem_orbitKernel_iff (H : Subgroup (Γ ≃g Γ)) [H.Normal] (g : Γ ≃g Γ) :
    g∈orbitKernel Γ H ↔ ∀ x, g x∈MulAction.orbit H x := by
  constructor
  · intro hg x
    have hh := congrArg (fun p : Equiv.Perm (NormalOrbit.Blocks (X := X) H) =>
      p (NormalOrbit.block H x)) hg
    exact (NormalOrbit.block_eq_iff H (g x) x).mp hh
  · intro hg
    apply Equiv.ext
    intro b
    induction b using Quotient.inductionOn with
    | h x => exact (NormalOrbit.block_eq_iff H (g x) x).mpr (hg x)

lemma le_orbitKernel (H : Subgroup (Γ ≃g Γ)) [H.Normal] : H≤orbitKernel Γ H :=
  NormalOrbit.le_ker_blockHom H

variable [TopologicalSpace X] [DiscreteTopology X]
local instance : TopologicalSpace (Γ ≃g Γ) := autTopology Γ

lemma orbitKernel_closed (H : Subgroup (Γ ≃g Γ)) [H.Normal] :
    IsClosed (orbitKernel Γ H : Set (Γ ≃g Γ)) := by
  have he : (orbitKernel Γ H : Set (Γ ≃g Γ))=
      ⋂ x : X, {g : Γ ≃g Γ | g x∈MulAction.orbit H x} := by
    ext g
    simp only [Set.mem_iInter,Set.mem_ofPred_eq,SetLike.mem_coe,mem_orbitKernel_iff]
  rw [he]
  exact isClosed_iInter (fun x => isClosed_eval_mem Γ x _)

lemma compact_orbitKernel (H : Subgroup (Γ ≃g Γ)) [H.Normal]
    (hH : IsCompact (H : Set (Γ ≃g Γ))) :
    IsCompact (orbitKernel Γ H : Set (Γ ≃g Γ)) := by
  have hfin : ∀ x : X, (MulAction.orbit H x).Finite := by
    intro x
    have hh := compact_finite_vertex_images Γ (H : Set (Γ ≃g Γ)) hH x
    apply hh.subset
    rintro y ⟨h,rfl⟩
    exact ⟨h.val,h.property,rfl⟩
  apply (compact_coordinate_bounds Γ (MulAction.orbit H) hfin).of_isClosed_subset
    (orbitKernel_closed Γ H)
  intro g hg
  exact ⟨(mem_orbitKernel_iff Γ H g).mp hg,
    (mem_orbitKernel_iff Γ H g⁻¹).mp ((orbitKernel Γ H).inv_mem hg)⟩

lemma open_orbitKernel_of_locallyConnected_quotient
    (H : Subgroup (Γ ≃g Γ)) [H.Normal]
    [LocallyConnectedSpace ((Γ ≃g Γ) ⧸ H)] :
    IsOpen (orbitKernel Γ H : Set (Γ ≃g Γ)) := by
  let B := NormalOrbit.Blocks (X := X) H
  let _ : TopologicalSpace B := ⊥
  let _ : DiscreteTopology B := ⟨rfl⟩
  have hcont : ∀ x : X, Continuous (fun q : (Γ ≃g Γ) ⧸ H =>
      q • (NormalOrbit.block H x : B)) := by
    intro x
    apply (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr
    change Continuous (fun g : Γ ≃g Γ => NormalOrbit.block H (g x))
    exact (continuous_of_discreteTopology : Continuous (NormalOrbit.block (X := X) H)).comp
      (continuous_eval Γ x)
  have hsub : (QuotientGroup.mk' H) ⁻¹'
      connectedComponent (1 : (Γ ≃g Γ) ⧸ H) ⊆ (orbitKernel Γ H : Set (Γ ≃g Γ)) := by
    intro g hg
    apply (mem_orbitKernel_iff Γ H g).mpr
    intro x
    have hh := ((isPreconnected_connectedComponent (x := (1 : (Γ ≃g Γ) ⧸ H))).image
      (fun q : (Γ ≃g Γ) ⧸ H => q • (NormalOrbit.block H x : B))
      (hcont x).continuousOn).subsingleton
    have he := hh ⟨QuotientGroup.mk' H g,hg,rfl⟩ ⟨1,mem_connectedComponent,rfl⟩
    apply (NormalOrbit.block_eq_iff H (g x) x).mp
    simpa only [NormalOrbit.mk_smul_block,one_smul,RelIso.smul_def] using he
  apply (orbitKernel Γ H).isOpen_of_mem_nhds (g := 1)
  apply Filter.mem_of_superset _ hsub
  apply (isOpen_connectedComponent.preimage QuotientGroup.continuous_mk).mem_nhds
  change (QuotientGroup.mk' H) 1∈connectedComponent (1 : (Γ ≃g Γ) ⧸ H)
  rw [map_one]
  exact mem_connectedComponent

theorem compact_open_orbitKernel_of_locallyConnected_quotient
    (H : Subgroup (Γ ≃g Γ)) [H.Normal]
    (hH : IsCompact (H : Set (Γ ≃g Γ)))
    [LocallyConnectedSpace ((Γ ≃g Γ) ⧸ H)] :
    IsCompact (orbitKernel Γ H : Set (Γ ≃g Γ)) ∧
      IsOpen (orbitKernel Γ H : Set (Γ ≃g Γ)) :=
  ⟨compact_orbitKernel Γ H hH,open_orbitKernel_of_locallyConnected_quotient Γ H⟩

theorem compact_open_orbitKernel_of_open_locallyConnected_subquotient
    (H L : Subgroup (Γ ≃g Γ)) [H.Normal]
    (hH : IsCompact (H : Set (Γ ≃g Γ))) (hL : IsOpen (L : Set (Γ ≃g Γ)))
    [LocallyConnectedSpace (L ⧸ H.subgroupOf L)] :
    IsCompact (orbitKernel Γ H : Set (Γ ≃g Γ)) ∧
      IsOpen (orbitKernel Γ H : Set (Γ ≃g Γ)) := by
  refine ⟨compact_orbitKernel Γ H hH,?_⟩
  let B := NormalOrbit.Blocks (X := X) H
  let _ : TopologicalSpace B := ⊥
  let _ : DiscreteTopology B := ⟨rfl⟩
  apply ConnectedAction.open_kernel_of_open_locallyConnected_subquotient
    (NormalOrbit.blockHom (X := X) H) _ L H hL (le_orbitKernel Γ H)
  intro b
  induction b using Quotient.inductionOn with
  | h x =>
    change Continuous (fun g : Γ ≃g Γ => NormalOrbit.block H (g x))
    exact (continuous_of_discreteTopology : Continuous (NormalOrbit.block (X := X) H)).comp
      (continuous_eval Γ x)

end CriticalPercolation.GraphTopology
end
end

end OAI
