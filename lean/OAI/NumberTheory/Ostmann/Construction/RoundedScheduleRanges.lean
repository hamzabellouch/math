import OAI.NumberTheory.Ostmann.Construction.ScheduledFrequencyBounds

namespace OAI

/-! # Rounded exponential bounds for the actual active and copied products -/

namespace Ostmann

open Filter
open scoped Topology BigOperators

/-- The interval step's two integer inequalities follow from the original
logarithmic product ranges with one uniform large-parameter threshold. -/
theorem eventually_rounded_schedule_ranges (C : ℝ) :
    ∀ᶠ m : ℝ in atTop, ∀ Δ : ℝ, 0 ≤ Δ → ∀ j : ℕ, ∀ T : ℝ,
      ∀ M B L K : ℕ,
      Real.exp (T - C) ≤ M → B ≤ naturalProductCap (T + C) →
      Real.exp (T + transferNextGap Δ m j - C) ≤ L →
      K ≤ naturalProductCap (T + transferNextGap Δ m j + C) →
      2 * B * naturalTransferCutoff Δ m j < L ∧
      2 * naturalTransferCutoff Δ m j * K ≤ naturalTransferCutoff Δ m (j + 1) * M := by
  filter_upwards [eventually_transfer_integer_ranges C] with m hm
  intro Δ hΔ j T M B L K hM hB hL hK
  obtain ⟨hg, hs⟩ := hm Δ hΔ j T M L hM hL
  exact ⟨(Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hB)).trans_lt hg,
    (Nat.mul_le_mul_left _ hK).trans hs⟩

end Ostmann

end OAI
