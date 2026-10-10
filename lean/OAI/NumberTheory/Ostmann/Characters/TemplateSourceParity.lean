import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePrefix
import OAI.NumberTheory.Ostmann.Characters.TemplateSourceTerminalNorm
import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalGramMean

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HistoryFrequencyLabels HistoryFrequencyBudget
open HigherBiasSourceWord HigherBiasSourceRoleBounds InitialCharacterScale Filter DiagonalEstimate
open ParityActions OneSidedPhase
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD) (B V : (l:ℕ) → State k (l+1) → ℤ) (n : ℕ)

abbrev sourceHistoryPairMean :=
  terminalHistoryPairMean k n (sourceWidth w.configuration (wordSize k L)) (wordSize k L)
    (by rw [sourceWidth_word]; omega)
    (sourceScheduledUnits w (n+1)) (sourceScheduledCharacters w (n+1)) (sourceScheduledCenters w (n+1))
    B V (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) (n+1))
    (sourceScheduledShells w (n+1)) (sourceScheduledShells_pos w (n+1))

theorem sourceParity_comparison {e : ℝ} (he : 0 ≤ e)
    (hpair : ∀σ τ : Reassignments k n (wordSize k L),σ≠τ →
      ∀h h',‖sourceHistoryPairMean w B V n σ τ h h'‖ ≤ e) :
    ‖sourceAmplitudeSequence w B V (n+1)‖^2 ≤
      (Fintype.card ↥(ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) (n+1) []) : ℝ)*
        (sourceRootEnergy w B V (n+1)/(factorialCount n (wordSize k L):ℝ)+
          (Fintype.card (SupportedHistory
            (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) (n+1)) (n+1) []) : ℝ)^2*e) := by
  have hm : wordSize k L ≤ sourceWidth w.configuration (wordSize k L) .word := by
    rw [sourceWidth_word]
    omega
  apply terminalParity_comparison k n (sourceWidth w.configuration (wordSize k L))
    (wordSize k L) hm (sourceScheduledUnits w (n+1)) (sourceScheduledCharacters w (n+1))
    (sourceScheduledCenters w (n+1)) B V
    (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) (n+1))
    (sourceScheduledShells w (n+1)) (sourceScheduledShells_pos w (n+1))
    (fun _ => s.locations.base 0)
    (scheduled_sourceShell_prefix w.configuration (wordSize k L) n hm
      (s.locations.base 0) (s.locations.base 2) s.locations.primes)
    (mul_nonneg (sq_nonneg _) he)
  intro σ τ hστ
  exact terminalParity_gram_norm_le k n (sourceWidth w.configuration (wordSize k L))
    (wordSize k L) hm (sourceScheduledUnits w (n+1)) (sourceScheduledCharacters w (n+1))
    (sourceScheduledCenters w (n+1)) B V
    (canonicalHistoryExtra k (DiagonalEstimate.sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) (n+1))
    (sourceScheduledShells w (n+1)) (sourceScheduledShells_pos w (n+1)) σ τ (hpair σ τ hστ)

end
end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
