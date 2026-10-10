import OAI.NumberTheory.TotientAsymptotic.FiniteMap

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic.FiniteMap

private lemma filter_card_le_sdiff_add {γ : Type*} [DecidableEq γ] (S E : Finset γ) (r : γ → Prop) :
    (S.filter r).card ≤ ((S \ E).filter r).card+E.card := by
  have hs : S.filter r ⊆ ((S \ E).filter r) ∪ E := by
    intro a ha
    by_cases he : a ∈ E
    · exact Finset.mem_union_right _ he
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp ha).1,he⟩,(Finset.mem_filter.mp ha).2⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

lemma filtered_card_comparison {α β : Type*} [DecidableEq α] [DecidableEq β] (T D : Finset α) (W B : Finset β)
    (F : α → β) (p : α → Prop) (q : β → Prop)
    (hbij : Set.BijOn F (↑(T \ D)) (↑(W \ B)))
    (hpred : ∀ a ∈ T \ D, p a ↔ q (F a)) :
    |((T.filter p).card : ℝ)-(W.filter q).card| ≤ D.card+B.card := by
  have heq : ((T \ D).filter p).card=((W \ B).filter q).card := by
    apply Finset.card_bij (fun a _ => F a)
    · intro a ha
      have ha' := (Finset.mem_filter.mp ha).1
      exact Finset.mem_filter.mpr ⟨hbij.1 ha',(hpred a ha').mp (Finset.mem_filter.mp ha).2⟩
    · intro a ha b hb hab
      exact hbij.2.1 (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
    · intro b hb
      obtain ⟨a,ha,hab⟩ := hbij.2.2 (Finset.mem_filter.mp hb).1
      refine ⟨a,Finset.mem_filter.mpr ⟨ha,?_⟩,hab⟩
      exact (hpred a ha).mpr (hab.symm ▸ (Finset.mem_filter.mp hb).2)
  have hT := filter_card_le_sdiff_add T D p
  have hW := filter_card_le_sdiff_add W B q
  have hsubT : ((T \ D).filter p).card ≤ (T.filter p).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
  have hsubW : ((W \ B).filter q).card ≤ (W.filter q).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
  rw [heq] at hT hsubT
  have h₁ : ((T.filter p).card : ℝ) ≤ ((W \ B).filter q).card+D.card := by exact_mod_cast hT
  have h₂ : ((W.filter q).card : ℝ) ≤ ((W \ B).filter q).card+B.card := by exact_mod_cast hW
  have h₃ : (((W \ B).filter q).card : ℝ) ≤ (T.filter p).card := by exact_mod_cast hsubT
  have h₄ : (((W \ B).filter q).card : ℝ) ≤ (W.filter q).card := by exact_mod_cast hsubW
  exact abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) D.card],by linarith [Nat.cast_nonneg (α := ℝ) B.card]⟩

end TotientAsymptotic.FiniteMap

end

end OAI
