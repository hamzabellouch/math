import Mathlib

namespace OAI

noncomputable section

namespace Problem315

theorem reach_target_by_neighbor_swaps
    {α β : Type*} [DecidableEq β]
    (r : α → α → Prop) (N : α → Finset β) (S : Finset β)
    (hcard : ∀ x, (N x).card = S.card)
    (hstep : ∀ x i j, i ∈ N x → i ∉ S → j ∈ S → j ∉ N x →
      ∃ y, r x y ∧ N y = insert j ((N x).erase i)) :
    ∀ x, ∃ y, Relation.ReflTransGen r x y ∧ N y = S := by
  classical
  have aux : ∀ k : ℕ, ∀ x, (S \ N x).card = k →
      ∃ y, Relation.ReflTransGen r x y ∧ N y = S := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x hk
      by_cases heq : N x = S
      · exact ⟨x, Relation.ReflTransGen.refl, heq⟩
      have hnotSN : ¬S ⊆ N x := by
        intro hsub
        exact heq (Finset.eq_of_subset_of_card_le hsub (hcard x).le).symm
      have hnotNS : ¬N x ⊆ S := by
        intro hsub
        exact heq (Finset.eq_of_subset_of_card_le hsub (hcard x).ge)
      obtain ⟨j, hjS, hjN⟩ := Finset.not_subset.mp hnotSN
      obtain ⟨i, hiN, hiS⟩ := Finset.not_subset.mp hnotNS
      obtain ⟨y, hxy, hNy⟩ := hstep x i j hiN hiS hjS hjN
      have hdiff : S \ N y = (S \ N x).erase j := by
        rw [hNy]
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        aesop
      have hj : j ∈ S \ N x := Finset.mem_sdiff.mpr ⟨hjS, hjN⟩
      have hlt : (S \ N y).card < k := by
        rw [hdiff, ← hk]
        exact Finset.card_erase_lt_of_mem hj
      obtain ⟨z, hyz, hz⟩ := ih (S \ N y).card hlt y rfl
      exact ⟨z, (Relation.ReflTransGen.single hxy).trans hyz, hz⟩
  intro x
  exact aux (S \ N x).card x rfl

end Problem315

end

end OAI
