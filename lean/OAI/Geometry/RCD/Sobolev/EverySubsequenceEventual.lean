import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace OAI

/-! # Eventual properties detected on further subsequences -/

open Filter
namespace RegularPointCoordinates

theorem eventually_of_every_subsequence (P : ℕ → Prop)
    (hP : ∀ α : ℕ → ℕ, StrictMono α → ∃ β : ℕ → ℕ,
      ∀ᶠ k in atTop, P (α (β k))) : ∀ᶠ k in atTop, P k := by
  by_contra hn
  obtain ⟨α,hα,hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp hn)
  obtain ⟨β,hβ⟩ := hP α hα
  obtain ⟨k,hk⟩ := hβ.exists
  exact hbad (β k) hk

end RegularPointCoordinates

end OAI
