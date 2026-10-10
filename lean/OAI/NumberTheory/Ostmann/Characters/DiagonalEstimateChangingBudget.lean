import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateChangingBudgetBasic
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateTotalCountActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate HistoryFrequencyBudget
open HistoryFrequencyLabels InitialCharacterScale Filter
attribute [local instance] Classical.propDecidable

theorem eventually_fixedConfiguration_changing_budget (d : Decomposition)
    {α β ρ γ c₀ c δ : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, ∀ BD : ℝ, 0 ≤ BD → ∃ K : ℝ, 0 < K ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ E : Finset ℕ, (∀ p ∈ E, p.Prime) →
      ∀ s : SelectedWordSource d E δ L k α β ρ γ c₀,
      ∀ w : FixedConfigurationWitness s c BD, ∀ j : ℕ, j ≤ k →
      copiedNormalization (actualCopiedShells w.configuration (wordSize k L) j
        (s.locations.base 0) (s.locations.base 2) s.locations.primes) *
        Real.exp (-gapSchedule BD k L (j+1)+sourceAtomWidth k c) *
        (Fintype.card (Equiv.Perm (ActualCopied w.configuration (wordSize k L) j)):ℝ) *
        (Fintype.card (SupportedHistory
          (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) j []):ℝ)^2 ≤
        Real.exp (K*L^2) := by
  filter_upwards [eventually_fixedConfiguration_copiedNormalization d hα hαβ hρ hγ hc₀ hc]
    with k hk
  intro BD hBD
  obtain ⟨K,hK,hcount⟩ := exists_fixedConfiguration_total_count_constant k BD hBD
  have hA := changingNormalizationCoefficient_nonneg k ρ c₀
  have hW : 0 ≤ sourceAtomWidth k c := zero_le_one.trans (sourceAtomWidth_ge_one k hc)
  refine ⟨changingNormalizationCoefficient k ρ c₀+sourceAtomWidth k c+K,by positivity,?_⟩
  filter_upwards [hk BD,hcount,eventually_ge_atTop (1:ℝ)] with L hnorm hcount hL
  intro E hE s w j hj
  have hC := (hnorm E hE s w j hj).trans
    (normalization_power_le_exp_quadratic k ρ c₀ hL hj)
  exact changing_scalar_budget hL hW (gapSchedule_nonneg_of_nonneg hBD k L (j+1))
    (Nat.cast_nonneg _) (sq_nonneg _) hC (hcount d E δ α β ρ γ c₀ c s w j hj)

end Ostmann.Characters.DiagonalEstimate

end

end OAI
