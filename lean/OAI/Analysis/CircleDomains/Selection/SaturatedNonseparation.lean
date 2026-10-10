import OAI.Analysis.CircleDomains.Selection.Nonseparation

namespace OAI

/-! A closed union of whole complementary components of a connected
open set is nonseparating. This allows clopen pieces of the compact
obstacle to be handled together in finite shrinking stages. -/
open Set Topology
namespace CircleDomainRigidity

lemma nonseparating_closed_saturated_complement
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [LocallyConnectedSpace X]
    {G A : Set X} (hG : IsOpen G) (hc : IsConnected G) (hA : IsClosed A)
    (hAF : A ⊆ Gᶜ)
    (hsat : ∀ x ∈ A, connectedComponentIn Gᶜ x ⊆ A) : IsConnected Aᶜ := by
  obtain ⟨a,ha⟩ := hc.nonempty
  have haA : a ∈ Aᶜ := fun h => hAF h ha
  have hcommon : ∀ x ∈ Aᶜ, a ∈ connectedComponentIn Aᶜ x := by
    intro x hx
    let V := connectedComponentIn Aᶜ x
    have hxV : x ∈ V := mem_connectedComponentIn hx
    have hVc : IsConnected V := isConnected_connectedComponentIn_iff.mpr hx
    have hVo : IsOpen V := hA.isOpen_compl.connectedComponentIn
    by_contra haV
    have hVF : V ⊆ Gᶜ := by
      intro y hy hyG
      have hGsub : G ⊆ connectedComponentIn Aᶜ y :=
        hc.isPreconnected.subset_connectedComponentIn hyG (fun z hz hzA => hAF hzA hz)
      have he : V = connectedComponentIn Aᶜ y := connectedComponentIn_eq hy
      apply haV
      change a ∈ V
      rw [he]
      exact hGsub ha
    have hVne : V ≠ univ := by
      intro he
      apply haV
      change a ∈ V
      rw [he]
      exact mem_univ a
    obtain ⟨z,hz⟩ := nonempty_frontier_iff.mpr ⟨⟨x,hxV⟩,hVne⟩
    have hznot : z ∉ V := by
      simpa only [hVo.interior_eq] using hz.2
    have hzA : z ∈ A := by
      by_contra hn
      let W := connectedComponentIn Aᶜ z
      have hzW : z ∈ W := mem_connectedComponentIn hn
      have hWo : IsOpen W := hA.isOpen_compl.connectedComponentIn
      obtain ⟨t,htW,htV⟩ := mem_closure_iff.mp hz.1 W hWo hzW
      have he : V=W := (connectedComponentIn_eq htV).trans (connectedComponentIn_eq htW).symm
      exact hznot (he.symm ▸ hzW)
    have hclVF : closure V ⊆ Gᶜ := hG.isClosed_compl.closure_subset_iff.mpr hVF
    have hclVsub : closure V ⊆ connectedComponentIn Gᶜ z :=
      hVc.closure.isPreconnected.subset_connectedComponentIn hz.1 hclVF
    exact hx (hsat z hzA (hclVsub (subset_closure hxV)))
  have he : connectedComponentIn Aᶜ a=Aᶜ := by
    apply Subset.antisymm (connectedComponentIn_subset _ _)
    intro x hx
    rw [← connectedComponentIn_eq (hcommon x hx)]
    exact mem_connectedComponentIn hx
  rw [← he]
  exact isConnected_connectedComponentIn_iff.mpr haA

lemma saturated_of_closed_relative_piece
    {X : Type*} [TopologicalSpace X] {F A : Set X}
    (hA : IsClosed A) (hFA : IsClosed (F \ A)) (hAF : A ⊆ F) :
    ∀ x ∈ A, connectedComponentIn F x ⊆ A := by
  intro x hx
  have hcomp := isPreconnected_connectedComponentIn (F := F) (x := x)
  have hcover : connectedComponentIn F x ⊆ A ∪ (F \ A) := by
    intro y hy
    by_cases hyA : y ∈ A
    · exact Or.inl hyA
    · exact Or.inr ⟨connectedComponentIn_subset _ _ hy,hyA⟩
  have hd : Disjoint A (F \ A) := Set.disjoint_left.mpr fun _ ha hb => hb.2 ha
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hcomp A (F \ A) hA hFA
    hcover (by rw [hd.inter_eq,inter_empty]) with h | h
  · exact h
  · exact (h (mem_connectedComponentIn (hAF hx))).2 hx |>.elim

lemma nonseparating_closed_relative_complement_piece
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [LocallyConnectedSpace X]
    {G A : Set X} (hG : IsOpen G) (hc : IsConnected G) (hA : IsClosed A)
    (hGA : IsClosed (Gᶜ \ A)) (hAF : A ⊆ Gᶜ) : IsConnected Aᶜ :=
  nonseparating_closed_saturated_complement hG hc hA hAF
    (saturated_of_closed_relative_piece hA hGA hAF)

end CircleDomainRigidity

end OAI
