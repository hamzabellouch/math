import Mathlib
import OAI.Probability.ThorpCompatibility.PermutationProbability

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
def MeetsLists {α β : Type*} (S : β × β → Finset α) (r : α → Equiv.Perm β) : Prop :=
  ∀ j k i, i ∈ S (j, k) → r i j = k

lemma lists_incidence_count {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

    (S : β × β → Finset α) (r : α → Equiv.Perm β) (hr : MeetsLists S r) :
    ∑ i, (Finset.univ.filter (fun j => i ∈ S (j, r i j))).card =
      ∑ b, (S b).card := by
  have hk (i : α) (j k : β) : i ∈ S (j, k) ↔ k = r i j ∧ i ∈ S (j, r i j) := by
    constructor
    · intro h
      exact ⟨(hr j k i h).symm, by simpa [hr j k i h] using h⟩
    · rintro ⟨rfl, h⟩
      exact h
  have hc (s : Finset α) : s.card = ∑ i, if i ∈ s then 1 else 0 := by simp
  calc
    _ = ∑ i, ∑ j, ∑ k, if i ∈ S (j, k) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro j _
      symm
      calc
        _ = ∑ k, if k = r i j then (if i ∈ S (j, r i j) then 1 else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases he : k = r i j
          · subst k
            simp
          · have hmem : i ∉ S (j, k) := fun h => he (hr j k i h).symm
            simp [he, hmem]
        _ = _ := by simp
    _ = ∑ j, ∑ k, ∑ i, if i ∈ S (j, k) then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type, hc]

lemma meetsLists_probability_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (hn : 0 < Fintype.card β)
    (S : β × β → Finset α) :
    uniformProbability (MeetsLists S) ≤
      (Real.exp 1 / Fintype.card β) ^ (∑ b, (S b).card) := by
  classical
  by_cases h : ∃ r, MeetsLists S r
  · obtain ⟨r, hr⟩ := h
    let s : α → Finset β := fun i => Finset.univ.filter (fun j => i ∈ S (j, r i j))
    have hP : MeetsLists S = (fun r' => ∀ i, ∀ j ∈ s i, r' i j = r i j) := by
      funext r'
      apply propext
      constructor
      · intro hr' i j hj
        exact hr' j (r i j) i ((Finset.mem_filter.mp hj).2)
      · intro hr' j k i hi
        have he := hr j k i hi
        have hm : j ∈ s i := by simpa [s, he] using hi
        exact (hr' i j hm).trans he
    rw [hP, uniformProbability_all (fun i (σ : Equiv.Perm β) => ∀ j ∈ s i, σ j = r i j)]
    calc
      _ ≤ ∏ i, (Real.exp 1 / Fintype.card β) ^ (s i).card := by
        apply Finset.prod_le_prod₀
        · intro i _
          exact uniformProbability_nonneg _
        · intro i _
          rw [uniformProbability_def]
          exact prescribed_function_probability_le hn (s i) (r i)
      _ = (Real.exp 1 / Fintype.card β) ^ (∑ i, (s i).card) :=
        Finset.prod_pow_eq_pow_sum Finset.univ _ _
      _ = _ := by rw [lists_incidence_count S r hr]
  · rw [uniformProbability_eq_zero _ h]
    positivity

end ThorpCompatibility

end OAI
