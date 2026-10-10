import OAI.NumberTheory.Ostmann.Arithmetic.BulkWeightedCost

namespace OAI

/-! # Uniform decay of the full weighted bulk replacement error -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The cutoff is chosen before the finite cell sets, modulus and original
normalizers. Their literal bounds include every joint box and residue. -/
theorem PublishedProgressionInput.bulk_weighted_error_rate
    (P : PublishedProgressionInput) (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (J Cell : Type) [Fintype J] [Fintype Cell]
      (M Q : ℕ) [NeZero M], 2 ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 10000 : ℝ) * L) →
      ∀ (Z : J → ℝ) (a : (J → (ZMod M)ˣ) → ℂ) (A B T : ℝ),
      (∀ j, 0 ≤ Z j) → 0 ≤ A → 0 ≤ B →
      (Fintype.card J : ℝ) ≤ C * L →
      (∀ j, Z j ≤ Real.exp (C * L)) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (Fintype.card (ZMod M)ˣ : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L)) →
      A ≤ Real.exp (C * L * Real.exp ((1 / 1000 : ℝ) * L)) →
      B ≤ Real.exp (C * L ^ 2) →
      (∀ z, ‖a z‖ ≤ A) →
      Real.exp ((39 / 10000 : ℝ) * L) ≤ T →
      ∀ u : J → Cell → ℝ, (∀ j c, T ≤ u j c) →
      (∏ j, Z j) * ∑ c : J → Cell, ∑ z : J → (ZMod M)ˣ, ‖a z‖ *
        (2 ^ Fintype.card J * ∑ j, B * bulkPrimeErrorFactor P Q (u j (c j))) ≤
      Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) := by
  filter_upwards [P.bulk_full_progression_budget_rate (8 * C ^ 2) 2,
    eventually_ge_atTop (1 : ℝ)] with L hrate hL
  intro J Cell _ _ M Q _ hQ hlog Z a A B T hZ0 hA0 hB0 hJ hZ hcell hunit hA hB ha hT u hu
  let V := (∏ j, Z j) * (Fintype.card Cell : ℝ) ^ Fintype.card J *
    (Fintype.card (ZMod M)ˣ : ℝ) ^ Fintype.card J * A *
      2 ^ Fintype.card J * (Fintype.card J : ℝ) * B
  have hV : V ≤ Real.exp (8 * C ^ 2 * L ^ 2 +
      8 * C ^ 2 * L * Real.exp ((14 / 10000 : ℝ) * L)) :=
    bulk_weighted_cost_le_exp M Z A B C L hC hL hZ0 hA0 hB0 hJ hZ hcell hunit hA hB
  exact (bulk_weighted_error_budget P hQ Z hZ0 a A hA0 ha u T hu B hB0).trans
    (hrate Q hQ hlog T V hT hV)

end Ostmann

end OAI
