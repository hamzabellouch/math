import OAI.Dynamics.ConditionalShuffle.PhysicalInstrument

namespace OAI

noncomputable section
namespace Revealed
open scoped Classical
open Thorp

lemma imageRank_lt_iff {α β : Type*} [Fintype α] [LinearOrder β]
    (f : α → β) (hf : Function.Injective f) (a b : α) :
    imageRank f hf a < imageRank f hf b ↔ f a < f b := by
  unfold imageRank
  exact (Fintype.orderIsoFinOfCardEq (Set.range f)
    (Fintype.card_congr (Equiv.ofInjective f hf)).symm).symm.lt_iff_lt

lemma imageRank_comp_perm {α β : Type*} [Fintype α] [LinearOrder β]
    (f : α → β) (hf : Function.Injective f) (g : Equiv.Perm α) :
    imageRank (f ∘ g) (hf.comp g.injective) = g.trans (imageRank f hf) := by
  let e := (imageRank (f ∘ g) (hf.comp g.injective)).symm.trans (g.trans (imageRank f hf))
  have he : StrictMono e := by
    intro i j hij
    change imageRank f hf (g ((imageRank (f ∘ g) (hf.comp g.injective)).symm i)) <
      imageRank f hf (g ((imageRank (f ∘ g) (hf.comp g.injective)).symm j))
    rw [imageRank_lt_iff]
    exact (imageRank_lt_iff (f ∘ g) (hf.comp g.injective) _ _).mp (by simpa using hij)
  let o : Fin (Fintype.card α) ≃o Fin (Fintype.card α) :=
    { toEquiv := e, map_rel_iff' := fun {_ _} => he.le_iff_le }
  have ho : o = OrderIso.refl _ := Subsingleton.elim _ _
  apply Equiv.ext
  intro a
  have ha := congrArg (fun h : Fin (Fintype.card α) ≃o Fin (Fintype.card α) =>
    h (imageRank (f ∘ g) (hf.comp g.injective) a)) ho
  simpa [o, e] using ha.symm

def splitLabels (d : ℕ) : Sum (Position d) (Position d) ≃ Position (d+1) where
  toFun
    | .inl x => outside d x
    | .inr x => freeLabel d x
  invFun x := if x 0 then .inl (Fin.tail x) else .inr (Fin.tail x)
  left_inv x := by cases x <;> simp [outside, freeLabel]
  right_inv x := by
    cases h : x 0 <;> simpa only [h, Bool.false_eq_true, ite_false, ite_true, outside, freeLabel]
      using (Fin.cons_self_tail x)

lemma splitLabels_inl (d : ℕ) (x : Position d) : splitLabels d (.inl x) = outside d x := rfl
lemma splitLabels_inr (d : ℕ) (x : Position d) : splitLabels d (.inr x) = freeLabel d x := rfl

namespace Split
variable {ι : Type} (d : ℕ)

def ranks (L : Sum ι (Position d) ≃ Position (d+1)) : Position d ≃ Fin (2^d) :=
  (imageRank (fun a => toLex (L (.inr a))) (by intro a b h; exact Sum.inr_injective (L.injective h))).trans
    (finCongr (by simp [Position]))

lemma ranks_pre (L : Sum ι (Position d) ≃ Position (d+1)) (g : State d) :
    ranks d ((Equiv.sumCongr (Equiv.refl ι) g).trans L) = g.trans (ranks d L) := by
  unfold ranks
  have hh := imageRank_comp_perm (fun a => toLex (L (.inr a)))
    (by intro a b h; exact Sum.inr_injective (L.injective h)) g
  exact congrArg (fun E : Position d ≃ Fin (Fintype.card (Position d)) =>
    E.trans (finCongr (show Fintype.card (Position d) = 2^d by simp [Position]))) hh

lemma ranks_assignment (L : Sum ι (Position d) ≃ Position (d+1)) :
    ranks d L = (assignment L).trans (ranks d (sectionFrame (outside L))) := by
  conv_lhs => rw [← assignment_factor L]
  rw [ranks_pre]

lemma ranks_freeRank (g : State (d+1)) : ranks d ((splitLabels d).trans g) = freeRank d g := rfl

end Split
end Revealed

end

end OAI
