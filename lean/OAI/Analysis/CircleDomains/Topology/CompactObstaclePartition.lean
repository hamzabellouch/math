import OAI.Analysis.CircleDomains.Topology.CompactClopenPartition

namespace OAI

/-! A finite relatively clopen partition of a compact plane obstacle,
subordinate to open neighborhoods of its whole components. -/
open Set Topology
noncomputable section
namespace CircleDomainRigidity

lemma compact_obstacle_partition
    {F : Set ℂ} (hF : IsCompact F) (O : F → Set ℂ)
    (hO : ∀ x, IsOpen (O x))
    (hcomp : ∀ x : F, connectedComponentIn F x.val ⊆ O x) :
    ∃ (s : Finset F) (A : s → Set ℂ),
      (∀ i, IsCompact (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (⋃ i, A i) = F ∧ (∀ i, A i ⊆ O i.val) ∧
      (∀ i, A i ⊆ F) ∧ ∀ i, IsClosed (F \ A i) := by
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF
  have hcomponent (x : F) : connectedComponent x ⊆ Subtype.val ⁻¹' O x := by
    intro y hy
    apply hcomp x
    rw [connectedComponentIn_eq_image x.property]
    exact ⟨y,hy,rfl⟩
  obtain ⟨s,C,hC,hd,hcover,hCO⟩ := compact_clopen_partition_of_component_cover
    (fun x : F => Subtype.val ⁻¹' O x)
    (fun x => (hO x).preimage continuous_subtype_val) hcomponent
  let A (i : s) : Set ℂ := Subtype.val '' C i
  have hAF (i : s) : A i ⊆ F := by
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  refine ⟨s,A,fun i => (hC i).isClosed.isCompact.image continuous_subtype_val,?_,?_,?_,hAF,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨a,ha,he⟩ ⟨b,hb,hbval⟩
    have hab : a=b := Subtype.ext (he.trans hbval.symm)
    exact Set.disjoint_left.mp (hd hij) ha (hab.symm ▸ hb)
  · apply Subset.antisymm
    · exact iUnion_subset hAF
    · intro x hx
      have hh : (⟨x,hx⟩ : F) ∈ ⋃ i, C i := by rw [hcover]; trivial
      obtain ⟨i,hi⟩ := mem_iUnion.mp hh
      exact mem_iUnion.mpr ⟨i,⟨⟨x,hx⟩,hi,rfl⟩⟩
  · intro i x hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact hCO i hy
  · intro i
    have he : F \ A i = Subtype.val '' (C i)ᶜ := by
      ext x
      constructor
      · rintro ⟨hxF,hxA⟩
        exact ⟨⟨x,hxF⟩,fun h => hxA ⟨⟨x,hxF⟩,h,rfl⟩,rfl⟩
      · rintro ⟨x,hx,rfl⟩
        refine ⟨x.property,?_⟩
        rintro ⟨y,hy,hyx⟩
        exact hx (Subtype.ext hyx ▸ hy)
    rw [he]
    exact hF.isClosed.isClosedMap_subtype_val _ (hC i).isOpen.isClosed_compl

end CircleDomainRigidity

end

end OAI
