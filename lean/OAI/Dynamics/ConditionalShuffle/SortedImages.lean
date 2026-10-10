import OAI.Dynamics.ConditionalShuffle.ColorProduct

namespace OAI

noncomputable section
namespace Revealed
open scoped Classical

def sortedImage {α β : Type} [Fintype α] [LinearOrder β]
    (f : α → β) (hf : Function.Injective f) (i : Fin (Fintype.card α)) : β :=
  f ((imageRank f hf).symm i)

lemma sortedImage_strictMono {α β : Type} [Fintype α] [LinearOrder β]
    (f : α → β) (hf : Function.Injective f) : StrictMono (sortedImage f hf) := by
  intro i j hij
  apply (imageRank_lt_iff f hf _ _).mp
  simpa only [Equiv.apply_symm_apply] using hij

lemma range_sortedImage {α β : Type} [Fintype α] [LinearOrder β]
    (f : α → β) (hf : Function.Injective f) : Set.range (sortedImage f hf) = Set.range f := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨(imageRank f hf).symm i,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨imageRank f hf a, by simp only [sortedImage, Equiv.symm_apply_apply]⟩

lemma sortedImage_eq_of_range {α β : Type} [Fintype α] [LinearOrder β]
    (f g : α → β) (hf : Function.Injective f) (hg : Function.Injective g)
    (hr : Set.range f = Set.range g) : sortedImage f hf = sortedImage g hg := by
  let e : α ≃ α := (Equiv.ofInjective f hf).trans
    ((Set.equivOfEq hr).trans (Equiv.ofInjective g hg).symm)
  have he : g ∘ e = f := by
    funext a
    have hh := (Equiv.ofInjective g hg).apply_symm_apply ((Set.equivOfEq hr) (Equiv.ofInjective f hf a))
    exact congrArg Subtype.val hh
  have hrank : imageRank f hf = e.trans (imageRank g hg) := by
    have hh := imageRank_comp_perm g hg e
    simpa only [he] using hh
  funext i
  change f ((imageRank f hf).symm i) = g ((imageRank g hg).symm i)
  calc
    _ = g (e ((imageRank f hf).symm i)) := (congrFun he _).symm
    _ = _ := by
      rw [hrank]
      simp only [Equiv.symm_trans, Equiv.trans_apply, Equiv.apply_symm_apply]

end Revealed

end

end OAI
