import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.RationalBranch

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {V : Type*} [LinearOrder V]
noncomputable def representative (S T : Finset V) : Finset (Fin S.card) :=
  Finset.univ.filter (fun i=>enum S i∈T)
lemma representative_image (S T : Finset V) (h : T⊆S) :
    (representative S T).image (enum S)=T := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hi).2
  · intro hx
    let i:=(equiv S).symm ⟨x,h hx⟩
    have hi : enum S i=x := by
      exact congrArg Subtype.val ((equiv S).apply_symm_apply ⟨x,h hx⟩)
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi ▸ hx⟩,hi⟩
lemma representative_card (S T : Finset V) (h : T⊆S) :
    (representative S T).card=T.card := by
  calc (representative S T).card = ((representative S T).image (enum S)).card :=
        (Finset.card_image_of_injective _ (enum_injective S)).symm
       _ = T.card := congrArg Finset.card (representative_image S T h)
end MetricKMedianRecovery.SortedIndex

end OAI
