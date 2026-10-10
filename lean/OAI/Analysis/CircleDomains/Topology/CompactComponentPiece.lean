import OAI.Analysis.CircleDomains.Topology.SmallPhysicalDisks

namespace OAI

/-! A whole component of a compact obstacle can be isolated inside any
prescribed open neighborhood by a compact relatively clopen piece. -/
open Set Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_compact_piece_of_component
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {F V : Set X} (hF : IsCompact F) {x : X} (hx : x ∈ F)
    (hV : IsOpen V) (hcomp : connectedComponentIn F x ⊆ V) :
    ∃ A : Set X, IsCompact A ∧ connectedComponentIn F x ⊆ A ∧
      A ⊆ F ∧ A ⊆ V ∧ IsClosed (F \ A) := by
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF
  let xf : F := ⟨x,hx⟩
  have hsub : connectedComponent xf ⊆ Subtype.val ⁻¹' V := by
    intro y hy
    apply hcomp
    rw [connectedComponentIn_eq_image hx]
    exact ⟨y,hy,rfl⟩
  obtain ⟨B,hB,hxB,hBV⟩ := exists_clopen_between_component_and_open xf
    (hV.preimage continuous_subtype_val) hsub
  let A : Set X := Subtype.val '' B
  have hdiff : F \ A = Subtype.val '' Bᶜ := by
    ext y
    constructor
    · rintro ⟨hyF,hyA⟩
      exact ⟨⟨y,hyF⟩,fun h => hyA ⟨⟨y,hyF⟩,h,rfl⟩,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      refine ⟨y.property,?_⟩
      rintro ⟨z,hz,hzy⟩
      exact hy (Subtype.ext hzy ▸ hz)
  refine ⟨A,hB.isClosed.isCompact.image continuous_subtype_val,?_,?_,?_,?_⟩
  · intro y hy
    rw [connectedComponentIn_eq_image hx] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    exact ⟨z,hB.connectedComponent_subset hxB hz,rfl⟩
  · rintro _ ⟨y,_,rfl⟩
    exact y.property
  · rintro _ ⟨y,hy,rfl⟩
    exact hBV hy
  · rw [hdiff]
    exact hF.isClosed.isClosedMap_subtype_val _ hB.isOpen.isClosed_compl

end CircleDomainRigidity

end

end OAI
