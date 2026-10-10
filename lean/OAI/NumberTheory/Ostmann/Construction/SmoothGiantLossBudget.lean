import OAI.NumberTheory.Ostmann.Construction.SmoothLogCellProfile
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale

namespace OAI

/-! # The actual giant normalization fits the iteration reserve -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- Taking the positive part only enlarges the transfer loss. For every
center in the paper's range, the sum of these actual losses fits the even
bulk count, including the factor two reserved at each step. -/
theorem PublishedProgressionInput.smoothGiant_iteration_budget
    (P : PublishedProgressionInput) (k : ℕ) (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀ G : ℕ → ℝ,
      (∀ j < k, 2 ≤ G j) →
      (∀ j < k, Real.exp ((39 / 10000 : ℝ) * L) ≤ G j - 1 / 2) →
      (∀ j < k, G j ≤ Real.exp ((9 / 10 : ℝ) * L)) →
      ∑ j ∈ Finset.range k,
        (max 0 (smoothGiantLogNormalizer (smoothGiantPrimeRange (G j)) logCellProfile (G j)) +
          Real.log 2) ≤ (spectatorBulkCount k L : ℝ) := by
  filter_upwards [P.logCellProfile_normalizer_rate (9 / 10), eventually_ge_atTop (1 : ℝ)]
    with L hrate hL
  intro G hG hlo hhi
  have hscale : 4 ≤ (k : ℝ) ^ 4 * L := by
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hk' 4
    nlinarith
  apply spectatorBulkCount_iteration_budget k hk L hL hscale
  intro j hj
  apply max_le (by linarith)
  have hh := (hrate (G j) (hG j hj) (hlo j hj) (hhi j hj)).2.1
  norm_num at hh
  exact hh

end Ostmann

end OAI
