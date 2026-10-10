import OAI.Analysis.CircleDomains.Topology.ComponentTopology
import Mathlib.Topology.Connected.LocallyConnected

namespace OAI

/-!
# Nonseparation of complementary components

Complementary components of a connected sphere domain do not separate
the sphere, as required by Moore's 1925 decomposition theorem.
-/

open Set Topology

namespace CircleDomainRigidity

private theorem isClosed_componentIn {X : Type*} [TopologicalSpace X]
    {F : Set X} (hF : IsClosed F) (x : X) : IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · rw [connectedComponentIn_eq_image hx]
    exact hF.isClosedMap_subtype_val _ isClosed_connectedComponent
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-- In a connected locally connected space, every complementary component of
a nonempty connected open set is nonseparating. -/
theorem nonseparating_complementaryComponent
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [LocallyConnectedSpace X]
    {G : Set X} (hopen : IsOpen G) (hconn : IsConnected G) {p : X} (hp : p ∉ G) :
    IsConnected (connectedComponentIn Gᶜ p)ᶜ := by
  let Q := connectedComponentIn Gᶜ p
  have hQF : Q ⊆ Gᶜ := connectedComponentIn_subset _ _
  have hQclosed : IsClosed Q := isClosed_componentIn hopen.isClosed_compl p
  have hQconn : IsConnected Q := isConnected_connectedComponentIn_iff.mpr hp
  obtain ⟨a, ha⟩ := hconn.nonempty
  have haQ : a ∈ Qᶜ := fun ha' => hQF ha' ha
  have hcommon : ∀ x ∈ Qᶜ, a ∈ connectedComponentIn Qᶜ x := by
    intro x hx
    let V := connectedComponentIn Qᶜ x
    have hxV : x ∈ V := mem_connectedComponentIn hx
    have hVconn : IsConnected V := isConnected_connectedComponentIn_iff.mpr hx
    have hVopen : IsOpen V := hQclosed.isOpen_compl.connectedComponentIn
    by_contra haV
    have hVF : V ⊆ Gᶜ := by
      intro y hyV hyG
      have hGy : G ⊆ connectedComponentIn Qᶜ y :=
        hconn.isPreconnected.subset_connectedComponentIn hyG
          (fun z hz hQz => hQF hQz hz)
      have heq : V = connectedComponentIn Qᶜ y := connectedComponentIn_eq hyV
      apply haV
      change a ∈ V
      rw [heq]
      exact hGy ha
    have hVne : V ≠ univ := by
      intro h
      apply haV
      change a ∈ V
      rw [h]
      exact mem_univ a
    obtain ⟨z, hz⟩ := nonempty_frontier_iff.mpr ⟨⟨x, hxV⟩, hVne⟩
    have hznotV : z ∉ V := by
      have hn : z ∉ interior V := hz.2
      simpa only [hVopen.interior_eq] using hn
    have hzQ : z ∈ Q := by
      by_contra hzQ
      let W := connectedComponentIn Qᶜ z
      have hzW : z ∈ W := mem_connectedComponentIn hzQ
      have hWopen : IsOpen W := hQclosed.isOpen_compl.connectedComponentIn
      obtain ⟨t, htW, htV⟩ := mem_closure_iff.mp hz.1 W hWopen hzW
      have heq : V = W :=
        (connectedComponentIn_eq htV).trans (connectedComponentIn_eq htW).symm
      exact hznotV (heq.symm ▸ hzW)
    have hclVF : closure V ⊆ Gᶜ :=
      hopen.isClosed_compl.closure_subset_iff.mpr hVF
    have hunion : IsConnected (Q ∪ closure V) :=
      hQconn.union ⟨z, hzQ, hz.1⟩ hVconn.closure
    have hmax : Q ∪ closure V ⊆ Q :=
      hunion.isPreconnected.subset_connectedComponentIn
        (Or.inl (mem_connectedComponentIn hp)) (union_subset hQF hclVF)
    exact hx (hmax (Or.inr (subset_closure hxV)))
  have heq : connectedComponentIn Qᶜ a = Qᶜ := by
    apply Set.Subset.antisymm (connectedComponentIn_subset _ _)
    intro x hx
    rw [← connectedComponentIn_eq (hcommon x hx)]
    exact mem_connectedComponentIn hx
  rw [← heq]
  exact isConnected_connectedComponentIn_iff.mpr haQ

end CircleDomainRigidity

end OAI
