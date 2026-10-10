import OAI.Analysis.CircleDomains.Selection.TagValidity
import OAI.Analysis.CircleDomains.Topology.ComponentLocalization

namespace OAI

/-! A nonconstant active tag lies in a nontrivial connected component
through each of its interior image points. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
theorem nontrivial_component_of_tag (γ : C(PathTime, X)) (s : TagSlot)
    (hshape : (γ, s) ∈ validTagShape) (A : Set X)
    (hcontain : ∀ t, tagLeft s < t → t < tagRight s → γ t ∈ A)
    (t : PathTime) (hl : tagLeft s < t) (hr : t < tagRight s) :
    (connectedComponentIn A (γ t)).Nontrivial := by
  have hnonconstant : (γ, s) ∈ nonconstantTagSegment := by
    rcases hshape with h | h
    · obtain ⟨u, hu⟩ := h
      change Sum.inl u = s at hu
      rw [← hu] at hl
      exact (not_lt_of_ge le_top hl).elim
    · exact h
  obtain ⟨a, b, ha, ha', hb, hb', hab⟩ := hnonconstant
  have hconn : IsPreconnected (γ '' Ioo (tagLeft s) (tagRight s)) :=
    isPreconnected_Ioo.image γ γ.continuous.continuousOn
  have hsub : γ '' Ioo (tagLeft s) (tagRight s) ⊆ A := by
    rintro x ⟨u, hu, rfl⟩
    exact hcontain u hu.1 hu.2
  have hcc := hconn.subset_connectedComponentIn (mem_image_of_mem γ ⟨hl, hr⟩) hsub
  exact ⟨γ a, hcc (mem_image_of_mem γ ⟨ha, ha'⟩),
    γ b, hcc (mem_image_of_mem γ ⟨hb, hb'⟩), hab⟩

omit [T2Space X] in
theorem active_tag_nontrivial_component
    (H : ℕ → Set (UnitAddCircle × X)) (γ : C(PathTime, X)) (q : TagData)
    (hshape : (γ, Sum.inr q) ∈ validTagShape)
    (hcontain : (γ, Sum.inr q) ∈ tagContainment H)
    (t : PathTime) (hl : tagLeft (Sum.inr q) < t) (hr : t < tagRight (Sum.inr q)) :
    (connectedComponentIn (⋃ j : Fin (q.1 + 1), {x | (q.2.2.1 j, x) ∈ H (q.2.1 j)})
      (γ t)).Nontrivial := by
  apply nontrivial_component_of_tag γ (Sum.inr q) hshape _ _ t hl hr
  intro u hu hu'
  exact mem_iUnion.mpr (hcontain u hu hu')

end CircleDomainRigidity

end

end OAI
