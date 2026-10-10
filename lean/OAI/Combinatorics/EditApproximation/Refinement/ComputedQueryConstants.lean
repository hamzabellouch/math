import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryMemo
import OAI.Combinatorics.EditApproximation.Refinement.ComputedPreparedWords
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryBudgetAlgebra

namespace OAI

namespace EditApproximation
open Filter

/-- The prepared record for the precise shared constants used by the memo. -/
theorem computedQueryParameters_numeric :
    ∀ᶠ N : ℕ in atTop, ∀ nx ny, nx + ny ≤ N → ∀ t, t ≤ inputHeight N ^ 2 → ∀ pass,
      BinaryFraction.PreparedKernelNumericBounds (nx := nx) (ny := ny) (M := (integerParameters N).M)
        N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (heightExponent N / 20) (smallLogExponent N)
        (inputHeight N ^ 8) (inputHeight N ^ 5)
        (inputHeight N ^ ((100 * (integerParameters N).M + 100000) *
          (coarseExponent (inputSmallLog N) + 1))) t
        (computedQueryParameters N 0).tau (computedQueryParameters N pass).factor
        (computedQueryParameters N 0).eta (computedQueryParameters N 0).kappa
        (computedQueryParameters N 0).delta (fun _ _ => 0) := by
  filter_upwards [computedPreparedWords_numeric] with N hn
  intro nx ny hsize t ht pass
  exact hn nx ny hsize t ht pass (inputSmallLog N).bits _ (bitWordValue_bits _)
    (by rw [← Nat.size_eq_bits_len]) (fun _ _ => 0) (by intros; simp)

theorem computedQueryMass_word :
    ∀ᶠ N : ℕ in atTop, Nat.size (localOnlineMassBound (integerParameters N).M
      (integerParameters N).P (inputHeight N)) ≤ inputHeight N := by
  filter_upwards [computedParameterPower_word,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hp hell
  have hH : 64 ≤ inputHeight N := hell.trans (computed_smallLog_le_height N)
  exact (Nat.size_le_size (computed_localOnlineMassBound_polynomial N hH)).trans
    (hp _ le_rfl)

theorem computedQueryInitialFactor_cap (N : ℕ) :
    (integerParameters N).initialFactor ≤ computedLocalKernelBudget 1 N := by
  unfold computedLocalKernelBudget localKernelPowerExponent
  change inputHeight N ^ (coarseExponent (inputSmallLog N) + 4) ≤ _
  apply Nat.pow_le_pow_right (Nat.two_pow_pos _)
  have h : 1 ≤ (integerParameters N).M :=
    one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))
  simp only [Nat.mul_one]
  nlinarith only [h, Nat.zero_le (coarseExponent (inputSmallLog N)),
    Nat.zero_le ((integerParameters N).M * coarseExponent (inputSmallLog N))]

end EditApproximation

end OAI
