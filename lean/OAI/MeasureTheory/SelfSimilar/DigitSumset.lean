import OAI.MeasureTheory.SelfSimilar.WordTypes

namespace OAI

universe uα uβ

section

open scoped BigOperators
namespace EntropyRateDimension
namespace DigitSumset

noncomputable def counts {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β] {k : ℕ}
    (w : Fin k → β → α) : β → α → Fin (k+1) := by
  classical
  exact fun j a => ⟨(Finset.univ.filter (fun t => w t j=a)).card,
    Nat.lt_succ_of_le ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Fintype.card_fin k))⟩

theorem counts_expand {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β] {k : ℕ}
    (v : β → α → ℝ) (w : Fin k → β → α) :
    ∑ t, ∑ j, v j (w t j) = ∑ j, ∑ a, ((counts w j a).val : ℝ)*v j a := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_fiberwise Finset.univ (fun t : Fin k => w t j)]
  apply Finset.sum_congr rfl
  intro a _
  calc
    ∑ t ∈ Finset.univ.filter (fun t : Fin k => w t j=a), v j (w t j) =
        ∑ _t ∈ Finset.univ.filter (fun t : Fin k => w t j=a), v j a := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [(Finset.mem_filter.mp ht).2]
    _ = _ := by simp [counts]

noncomputable def sumset (S : Finset ℝ) (k : ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun w : Fin k → S => ∑ t, (w t : ℝ))

theorem card_sumset_le {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β]
    (S : Finset ℝ) (v : β → α → ℝ)
    (hS : ∀ x ∈ S, ∃ w : β → α, x=∑ j, v j (w j)) (k : ℕ) :
    (sumset S k).card ≤ (k+1)^(Fintype.card β*Fintype.card α) := by
  classical
  let F : (β → α → Fin (k+1)) → ℝ := fun c => ∑ j, ∑ a, ((c j a).val : ℝ)*v j a
  have hin : sumset S k ⊆ Finset.univ.image F := by
    intro x hx
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
    choose w hw using (fun t => hS (u t) (u t).property)
    apply Finset.mem_image.mpr
    refine ⟨counts w,Finset.mem_univ _,?_⟩
    change (∑ j, ∑ a, ((counts w j a).val : ℝ)*v j a)=∑ t, (u t : ℝ)
    rw [← counts_expand]
    exact Finset.sum_congr rfl (fun t _ => (hw t).symm)
  calc
    (sumset S k).card ≤ (Finset.univ.image F).card := Finset.card_le_card hin
    _ ≤ (Finset.univ : Finset (β → α → Fin (k+1))).card := Finset.card_image_le
    _ = _ := by simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,← pow_mul]; rw [Nat.mul_comm]

end DigitSumset
end EntropyRateDimension

end

end OAI
