import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic

namespace OAI

/-! Finite mandatory mark sets that eventually contain every mark. -/

open Set Function Filter

namespace CircleDomainRigidity

theorem exists_increasing_finite_marks (S : Type*) [Countable S] :
    ∃ F : ℕ → Set S, (∀ n, (F n).Finite) ∧ Monotone F ∧
      ∀ s, ∀ᶠ n in atTop, s ∈ F n := by
  obtain ⟨e, he⟩ := exists_injective_nat S
  refine ⟨fun n => {s | e s < n + 1}, ?_, ?_, ?_⟩
  · intro n
    exact (Set.finite_lt_nat (n + 1)).preimage he.injOn
  · intro n m hnm s hs
    dsimp only [mem_ofPred_eq] at hs ⊢
    omega
  · intro s
    filter_upwards [eventually_ge_atTop (e s)] with n hn
    omega

theorem exists_increasing_finite_marks_inhabited (S : Type*) [Countable S] :
    ∃ F : ℕ → Set S, (∀ n, (F n).Finite) ∧ Monotone F ∧
      (∀ n, Nonempty S → (F n).Nonempty) ∧
      ∀ s, ∀ᶠ n in atTop, s ∈ F n := by
  classical
  obtain ⟨F, hF, hmono, hcover⟩ := exists_increasing_finite_marks S
  by_cases h : Nonempty S
  · let s := Classical.choice h
    refine ⟨fun n => F n ∪ {s}, fun n => (hF n).union (finite_singleton s), ?_, ?_, ?_⟩
    · exact fun n m hnm => union_subset_union_left _ (hmono hnm)
    · exact fun _ _ => ⟨s, Or.inr rfl⟩
    · exact fun x => (hcover x).mono (fun _ hx => Or.inl hx)
  · exact ⟨F, hF, hmono, fun _ hn => (h hn).elim, hcover⟩

end CircleDomainRigidity

end OAI
