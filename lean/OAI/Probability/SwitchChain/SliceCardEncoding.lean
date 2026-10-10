import OAI.Probability.SwitchChain.SliceReindexedComparison
import OAI.Probability.SwitchChain.SlicePermutationAction

namespace OAI

noncomputable section

namespace Problem315.SliceNormalized

variable {V Ω : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V] [sectionFintypeΩ : Fintype Ω]

def cardSliceEquiv (q : ℕ) : State V q ≃ SlicePermutationAction.Slice V q where
  toFun S := ⟨S.val, (Finset.mem_powersetCard.mp S.property).2⟩
  invFun S := ⟨S.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.property⟩⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv S := by apply Subtype.ext; rfl

include sectionDecidableEqV in
@[simp] theorem cardSliceEquiv_val (q : ℕ) (S : State V q) :
    (cardSliceEquiv q S).val = S.val := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

include sectionDecidableEqV in
@[simp] theorem cardSliceEquiv_symm_val (q : ℕ) (S : SlicePermutationAction.Slice V q) :
    ((cardSliceEquiv q).symm S).val = S.val := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  exact rfl

 theorem cardSliceEquiv_relabel (q : ℕ) (σ : Equiv.Perm V) (S : State V q) :
    cardSliceEquiv q (SliceEuclideanGenerator.relabel q σ S) =
      SlicePermutationAction.relabel σ (cardSliceEquiv q S) := by
  apply Subtype.ext
  simp [SlicePermutationAction.relabel, Finset.map_eq_image]

 theorem cardSliceEquiv_swap (q : ℕ) (i j : V) (S : State V q) :
    cardSliceEquiv q (SliceEuclideanGenerator.swapState q i j S) =
      SlicePermutationAction.relabel (Equiv.swap i j) (cardSliceEquiv q S) :=
  cardSliceEquiv_relabel q (Equiv.swap i j) S

include sectionFintypeΩ in
 theorem conjugated_swap_cardSlice {q : ℕ} (e : Ω ≃ SlicePermutationAction.Slice V q)
    (i j : V) (ω : Ω) :
    (e.trans (cardSliceEquiv q).symm).symm
      (SliceEuclideanGenerator.swapState q i j ((e.trans (cardSliceEquiv q).symm) ω)) =
      e.symm (SlicePermutationAction.relabel (Equiv.swap i j) (e ω)) := by
  have retainedsectionFintypeΩ := sectionFintypeΩ
  change e.symm (cardSliceEquiv q (SliceEuclideanGenerator.swapState q i j
    ((cardSliceEquiv q).symm (e ω)))) = _
  rw [cardSliceEquiv_swap, Equiv.apply_symm_apply]

end Problem315.SliceNormalized

end

end OAI
