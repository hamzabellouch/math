import OAI.Probability.DilutedSpin.ScheduledFrameGeometry

namespace OAI

section
section
namespace DilutedSpinGlass

/-- Finite labeling can pin both protected leaves without changing the full
leaf set; this is not an assumed identification of the two tree experiments. -/
lemma exists_equiv_two_points {α β : Type} [Fintype α] [Fintype β]
    (hcard : Fintype.card α=Fintype.card β) (a b : α) (c d : β)
    (hab : a≠b) (hcd : c≠d) : ∃ e : α ≃ β, e a=c ∧ e b=d := by
  classical
  let e₀ := Fintype.equivOfCardEq hcard
  let e₁ := e₀.trans (Equiv.swap (e₀ a) c)
  have ha : e₁ a=c := by simp [e₁]
  have hb : e₁ b≠c := by rw [← ha]; exact fun h => hab (e₁.injective h).symm
  refine ⟨e₁.trans (Equiv.swap (e₁ b) d),?_,?_⟩
  · simp only [Equiv.trans_apply,ha]
    exact Equiv.swap_apply_of_ne_of_ne hb.symm hcd
  · simp

namespace PrescribedTree

/-- Every split frame has a canonical Option/Fin dictionary labeling with
`none` and the FIRST inserted label at the protected corresponding twin leaves. -/
lemma splitFrame_canonical_labeling {n : ℕ} (S : PrescribedTree n) (r d t : ℕ)
    (b : S.Leaf) (hcard : Fintype.card (splitFrame S r d).Leaf=t+2) :
    ∃ q : Option (Fin (t+1)) ≃ (splitFrame S r d).Leaf,
      q none=splitFrameLeaf S r d 0 b ∧
      q (some (Fin.last t))=splitFrameLeaf S r d 1 b := by
  apply exists_equiv_two_points
  · simpa only [Fintype.card_option,Fintype.card_fin] using hcard.symm
  · simp
  · intro h
    have he := splitFrame_split S r d b
    rw [h,splitDepth_self] at he
    omega

end PrescribedTree
end DilutedSpinGlass
end

end

end OAI
