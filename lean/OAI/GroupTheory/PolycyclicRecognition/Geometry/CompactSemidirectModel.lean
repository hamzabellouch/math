import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectProductTopology
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangulableLieModel
import Mathlib.GroupTheory.Solvable

namespace OAI

/-! # Compact semidirect extensions used by the model comparison -/

noncomputable section
namespace PolycyclicRecognition
open Set

variable {G K : Type*} [Group G] [Group K] [TopologicalSpace G] [TopologicalSpace K]
  (α : K →* MulAut G)
attribute [local instance] semidirectProductTopology

omit [TopologicalSpace G] [TopologicalSpace K] in
theorem semidirect_solvable [Group.IsSolvable G] [Group.IsSolvable K] :
    Group.IsSolvable (G ⋊[α] K) :=
  Group.isSolvable_of_ker_le_range (SemidirectProduct.inl : G →* G ⋊[α] K)
    SemidirectProduct.rightHom SemidirectProduct.range_inl_eq_ker_rightHom.ge

theorem compactlyGenerated_compact_semidirect [CompactSpace K]
    (hG : ∃ U : Set G, IsCompact U ∧ Subgroup.closure U = ⊤) :
    ∃ U : Set (G ⋊[α] K), IsCompact U ∧ Subgroup.closure U = ⊤ := by
  obtain ⟨U,hU,hgen⟩ := hG
  let V := (SemidirectProduct.inl '' U : Set (G ⋊[α] K)) ∪ SemidirectProduct.inr '' univ
  refine ⟨V, (hU.image (continuous_semidirect_inl α)).union
    (isCompact_univ.image (continuous_semidirect_inr α)), ?_⟩
  apply top_unique
  intro p _
  have hn : p.left ∈ (Subgroup.closure V).comap (SemidirectProduct.inl : G →* G ⋊[α] K) := by
    have ht : (⊤ : Subgroup G) ≤ (Subgroup.closure V).comap SemidirectProduct.inl := by
      rw [← hgen]
      refine (Subgroup.closure_le _).mpr ?_
      intro g hg
      exact Subgroup.subset_closure (Or.inl ⟨g,hg,rfl⟩)
    exact ht (Subgroup.mem_top _)
  have hk : SemidirectProduct.inr p.right ∈ Subgroup.closure V :=
    Subgroup.subset_closure (Or.inr ⟨p.right,mem_univ _,rfl⟩)
  convert (Subgroup.closure V).mul_mem hn hk using 1
  exact (SemidirectProduct.inl_left_mul_inr_right p).symm

end PolycyclicRecognition

end

end OAI
