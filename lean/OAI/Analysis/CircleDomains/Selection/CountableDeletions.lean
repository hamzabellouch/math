import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Image
import Mathlib.Order.Filter.AtTopBot.Basic

namespace OAI

/-! Finite increasing deletions exhausting a prescribed countable mark set. -/

open Set Function Filter

noncomputable section
namespace CircleDomainRigidity

theorem exists_finite_deletions {X : Type*} (S : Set X) (hS : S.Countable) :
    ∃ F : ℕ → Finset X, Monotone F ∧ (∀ n, (F n : Set X) ⊆ S) ∧
      ∀ x ∈ S, ∀ᶠ n in atTop, x ∈ F n := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => ∅, fun _ _ _ => le_rfl, by simp, by simp⟩
  obtain ⟨f, rfl⟩ := hS.exists_eq_range hne
  refine ⟨fun n => (Finset.range n).image f, ?_, ?_, ?_⟩
  · intro m n hmn
    exact Finset.image_mono f (Finset.range_mono hmn)
  · intro n x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact mem_range_self i
  · rintro x ⟨i, rfl⟩
    exact eventually_atTop.2 ⟨i + 1, fun n hn =>
      Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self i) hn), rfl⟩⟩

theorem exists_countable_enumeration_with_default {I A : Type*} [Countable I]
    (f : I → A) (a₀ : A) :
    ∃ g : ℕ → A, (∀ i, ∃ n, g n = f i) ∧ ∀ n, g n = a₀ ∨ ∃ i, g n = f i := by
  let := Encodable.ofCountable I
  let g (n : ℕ) : A := (Encodable.decode (α := I) n).elim a₀ f
  refine ⟨g, ?_, ?_⟩
  · intro i
    exact ⟨Encodable.encode i, by simp [g]⟩
  · intro n
    cases h : Encodable.decode (α := I) n with
    | none => exact Or.inl (by simp [g, h])
    | some i => exact Or.inr ⟨i, by simp [g, h]⟩

end CircleDomainRigidity

end

end OAI
