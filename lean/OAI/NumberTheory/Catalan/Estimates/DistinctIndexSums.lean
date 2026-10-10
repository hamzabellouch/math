import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Max

namespace OAI


namespace InternalCatalan

open scoped BigOperators

private theorem shifted_range_card_sum_le (s : Finset ℕ) (b : ℕ)
    (hb : ∀ i ∈ s, b ≤ i) :
    (∑ k ∈ Finset.range s.card, (b + k)) ≤ ∑ i ∈ s, i := by
  revert hb
  induction s using Finset.induction_on_max with
  | empty => intro hb; simp
  | insert a s hmax ih =>
    intro hb
    have ha : a ∉ s := by
      intro ha
      exact (Nat.lt_irrefl a) (hmax a ha)
    have hba : b ≤ a := hb a (Finset.mem_insert_self a s)
    have hbs : ∀ i ∈ s, b ≤ i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hsub : s ⊆ Finset.Ico b a := by
      intro i hi
      exact Finset.mem_Ico.mpr ⟨hbs i hi, hmax i hi⟩
    have hcard : s.card ≤ a - b := by
      simpa only [Nat.card_Ico] using Finset.card_le_card hsub
    have hlast : b + s.card ≤ a := by omega
    have hsum := ih hbs
    rw [Finset.card_insert_of_notMem ha, Finset.sum_range_succ, Finset.sum_insert ha]
    omega

private theorem distinct_nat_sum_lower_of_le (s : Finset ℕ) (b : ℕ)
    (hb : ∀ i ∈ s, b ≤ i) :
    s.card * b + s.card * (s.card - 1) / 2 ≤ ∑ i ∈ s, i := by
  have hsum := shifted_range_card_sum_le s b hb
  have he : (∑ k ∈ Finset.range s.card, (b + k)) =
      s.card * b + s.card * (s.card - 1) / 2 := by
    calc
      _ = (∑ _ ∈ Finset.range s.card, b) +
          (∑ k ∈ Finset.range s.card, k) := Finset.sum_add_distrib
      _ = _ := by
        rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, Finset.sum_range_id]
  rwa [he] at hsum

theorem distinct_indices_sum_lower {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f (s : Set ι)) :
    s.card * (s.card - 1) / 2 ≤ ∑ i ∈ s, f i := by
  classical
  have h := distinct_nat_sum_lower_of_le (s.image f) 0 (by simp)
  rw [Finset.card_image_of_injOn hf, Finset.sum_image hf] at h
  simpa only [Nat.mul_zero, Nat.zero_add] using h

theorem distinct_indices_sum_lower_of_le {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f (s : Set ι)) (b : ℕ) (hb : ∀ i ∈ s, b ≤ f i) :
    s.card * b + s.card * (s.card - 1) / 2 ≤ ∑ i ∈ s, f i := by
  classical
  have himage : ∀ j ∈ s.image f, b ≤ j := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact hb i hi
  have h := distinct_nat_sum_lower_of_le (s.image f) b himage
  rw [Finset.card_image_of_injOn hf, Finset.sum_image hf] at h
  exact h

end InternalCatalan

end OAI
