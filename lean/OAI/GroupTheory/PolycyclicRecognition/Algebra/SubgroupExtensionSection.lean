import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExtensionSectionFactor

namespace OAI

/-! # Normalized extension sections with values in a surjective subgroup -/

noncomputable section
namespace PolycyclicRecognition
variable {N G Q : Type*} [Group N] [Group G] [Group Q]

theorem exists_normalized_section_in_subgroup (E : GroupExtension N G Q) (H : Subgroup G)
    (hs : Function.Surjective (E.rightHom.comp H.subtype)) :
    ∃ σ : E.Section, σ 1 = 1 ∧ ∀ q, σ q ∈ H := by
  classical
  let f : Q → H := Function.surjInv hs
  have hf : ∀ q, E.rightHom (f q) = q := Function.surjInv_eq hs
  let σ : E.Section :=
    { toFun q := if q = 1 then 1 else (f q : G)
      rightInverse_rightHom q := by
        change E.rightHom (if q = 1 then 1 else (f q : G)) = q
        split_ifs with h
        · simp only [h, map_one]
        · exact hf q }
  refine ⟨σ, ?_, ?_⟩
  · change (if (1 : Q) = 1 then (1 : G) else (f 1 : G)) = 1
    simp
  · intro q
    change (if q = 1 then (1 : G) else (f q : G)) ∈ H
    split_ifs
    · exact H.one_mem
    · exact (f q).property

end PolycyclicRecognition

end

end OAI
