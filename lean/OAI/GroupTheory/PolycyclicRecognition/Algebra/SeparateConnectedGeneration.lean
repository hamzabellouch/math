import OAI.GroupTheory.PolycyclicRecognition.Algebra.SeparateGroupClosure

namespace OAI

/-! # Connected generation with separately continuous operations

Two points in the image of a separately continuous two-variable map are
joined by two intersecting connected slices. A connected set containing
the identity then generates a connected subgroup, by taking the identity
component inside the generated subgroup itself.
-/

noncomputable section
namespace PolycyclicRecognition

theorem isPreconnected_image2_separate {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y → Z) (hf₁ : ∀ x, Continuous (f x))
    (hf₂ : ∀ y, Continuous (fun x => f x y))
    {s : Set X} {t : Set Y} (hs : IsPreconnected s) (ht : IsPreconnected t) :
    IsPreconnected (Set.image2 f s t) := by
  apply isPreconnected_of_forall_pair
  rintro _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ _ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
  refine ⟨f a₁ '' t ∪ (fun a => f a b₂) '' s, ?_,
    Or.inl ⟨b₁, hb₁, rfl⟩, Or.inr ⟨a₂, ha₂, rfl⟩, ?_⟩
  · rintro _ (⟨b, hb, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨a₁, ha₁, b, hb, rfl⟩
    · exact ⟨a, ha, b₂, hb₂, rfl⟩
  · exact (ht.image _ (hf₁ a₁).continuousOn).union (f a₁ b₂)
      ⟨b₂, hb₂, rfl⟩ ⟨a₁, ha₁, rfl⟩ (hs.image _ (hf₂ b₂).continuousOn)

variable {G : Type*} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [ContinuousInv G]

theorem isPreconnected_subgroup_closure {s : Set G} (hs : IsPreconnected s) (h1 : 1 ∈ s) :
    IsPreconnected (Subgroup.closure s : Set G) := by
  let H := Subgroup.closure s
  let : SeparatelyContinuousMul H :=
    Topology.IsInducing.subtypeVal.separatelyContinuousMul H.subtype
  let : ContinuousInv H := Topology.IsInducing.subtypeVal.continuousInv (fun _ => rfl)
  let T : Set H := H.subtype ⁻¹' s
  have he : H.subtype '' T = s := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hg
      exact ⟨⟨g, Subgroup.subset_closure hg⟩, hg, rfl⟩
  have hT : IsPreconnected T :=
    Topology.IsInducing.subtypeVal.isPreconnected_image.mp (he.symm ▸ hs)
  have hT1 : (1 : H) ∈ T := h1
  let C := separateIdentityComponent H
  have hsC : s ⊆ (C.map H.subtype : Set G) := by
    intro g hg
    let x : H := ⟨g, Subgroup.subset_closure hg⟩
    exact ⟨x, hT.subset_connectedComponent hT1 hg, rfl⟩
  have hHC : H ≤ C.map H.subtype := (Subgroup.closure_le _).mpr hsC
  have hC : C = ⊤ := by
    apply top_unique
    intro h _
    obtain ⟨c, hc, heq⟩ := hHC h.property
    have hh : c = h := Subtype.ext heq
    exact hh ▸ hc
  have hpre : IsPreconnected (Set.univ : Set H) := by
    have hc := separateIdentityComponent_preconnected (G := H)
    change IsPreconnected (C : Set H) at hc
    simpa only [hC, Subgroup.coe_top] using hc
  have himage := hpre.image H.subtype continuous_subtype_val.continuousOn
  have hrange : Set.range H.subtype = (H : Set G) := by
    ext g
    exact ⟨fun ⟨h, hh⟩ => hh ▸ h.property, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩
  simpa only [Set.image_univ, hrange] using himage

end PolycyclicRecognition

end

end OAI
