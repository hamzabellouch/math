import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFrequencyCutoff
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateInitialPrior
import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePhaseSupport
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateWindow

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HistoryFrequencyLabels HistoryFrequencyBudget
open HigherBiasSourceWord HigherBiasSourceRoleBounds InitialCharacterScale Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem source_amplitude_eq {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
    (E : Fin (sourceHalfSize cfg m) → Finset (PrimeUpTo Q))
    (hE : ∀ i,0 < primeShellMass (E i))
    (χ : Fin (sourceHalfSize cfg m) → (q:ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin (sourceHalfSize cfg m) → (q:ℕ) → ZMod q)
    (ζ : Fin (sourceHalfSize cfg m) → ℕ → ℂ)
    (B V : (j:ℕ) → State k (j+1) → ℤ) (R : ℕ → Finset ℕ+)
    (J : ℤ) (X Δ W : ℝ) (hX : 0 < X) (V₀ : ℕ)
    (hcut : Real.exp (Δ+W) ≤ 4*(V₀:ℝ))
    (S : List Bool → Finset ℤ) (hS : S [] = signedRange V₀)
    (hwindow : ∀ w : Fin (sourceHalfSize cfg m+sourceHalfSize cfg m) → PrimeUpTo Q,
      (∀ i,w i∈characterDoubleShell E i) →
      characterDoubleMask (sourceHalfMask J) w ≠ 0 →
      X*Real.exp (Δ-W) ≤ (characterTupleProduct w:ℝ) ∧
      (characterTupleProduct w:ℝ) ≤ X*Real.exp (Δ+W))
 :
    unitAmplitude k 0 (sourceWidth cfg m) (sourceUnitData cfg m ζ)
      (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a) B V
      (canonicalHistoryExtra k R) (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W))
      X Δ W S (sourcePrimeShells cfg m E) (sourcePrimeShells_positive cfg m E hE) =
    initialCharacterAmplitude (characterDoubleShell E) (characterDoubleShell_positive E hE)
      (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase ζ)
      (characterDoubleMask (sourceHalfMask J)) X := by
  exact source_amplitude_of_phase_support cfg m E hE χ a ζ B V R J X Δ W hX V₀ hcut S hS
    hwindow (fun w hw s hs=>sourceSample_currentAtomSupport cfg m χ a ζ w hw s PUnit.unit hs)

theorem fixedConfiguration_amplitude_eq {d : Decomposition} {E : Finset ℕ}
    {δ L : ℝ} {k : ℕ} {α β ρ γ c₀ c BD : ℝ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀}
    (w : FixedConfigurationWitness s c BD)
    (V₀ : ℕ) (hcut : Real.exp (initialGap BD k L+configurationProductWidth k c) ≤ 4*(V₀:ℝ))
    (B V : (j:ℕ) → State k (j+1) → ℤ) (R : ℕ → Finset ℕ+)
    (S : List Bool → Finset ℤ) (hS : S [] = signedRange V₀) :
    w.amplitude =
    unitAmplitude k 0 (sourceWidth w.configuration (wordSize k L))
      (sourceUnitData w.configuration (wordSize k L) (fun _=>familyPhase s.family))
      (sourceCharacterData w.configuration (wordSize k L) (fun _=>familyCharacter s.family))
      (sourceTranslationData w.configuration (wordSize k L) (fun _=>familyCenter s.family)) B V
      (canonicalHistoryExtra k R)
      (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
        (initialGap BD k L) (configurationProductWidth k c)))
      s.locations.X (initialGap BD k L) (configurationProductWidth k c) S
      (sourcePrimeShells w.configuration (wordSize k L) w.roles)
      (sourcePrimeShells_positive w.configuration (wordSize k L) w.roles w.roles_pos) := by
  exact (source_amplitude_eq w.configuration (wordSize k L) w.roles w.roles_pos
    (fun _=>familyCharacter s.family) (fun _=>familyCenter s.family) (fun _=>familyPhase s.family)
    B V R s.J s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (fixedConfiguration_X_pos w) V₀ hcut S hS
    (fun q hq=>fixedConfiguration_product_window w (fixedConfiguration_X_pos w) q hq)).symm

theorem eventually_fixedConfiguration_amplitude_eq (k : ℕ) (BD : ℝ) (hBD : 0 ≤ BD)
    (c : ℝ) :
    ∀ᶠ L : ℝ in atTop,∀ (d : Decomposition) (E : Finset ℕ) (δ α β ρ γ c₀ : ℝ),
    ∀ (s : SelectedWordSource d E δ L k α β ρ γ c₀) (w : FixedConfigurationWitness s c BD),
    ∀ (B V : (j:ℕ) → State k (j+1) → ℤ) (R : ℕ → Finset ℕ+),
    w.amplitude =
    unitAmplitude k 0 (sourceWidth w.configuration (wordSize k L))
      (sourceUnitData w.configuration (wordSize k L) (fun _=>familyPhase s.family))
      (sourceCharacterData w.configuration (wordSize k L) (fun _=>familyCharacter s.family))
      (sourceTranslationData w.configuration (wordSize k L) (fun _=>familyCenter s.family)) B V
      (canonicalHistoryExtra k R)
      (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
        (initialGap BD k L) (configurationProductWidth k c)))
      s.locations.X (initialGap BD k L) (configurationProductWidth k c)
      (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) 0)
      (sourcePrimeShells w.configuration (wordSize k L) w.roles)
      (sourcePrimeShells_positive w.configuration (wordSize k L) w.roles w.roles_pos) := by
  filter_upwards [eventually_initial_frequency_budget_covers_width k BD hBD
    (configurationProductWidth k c)] with L hcut
  intro d E δ α β ρ γ c₀ s w B V R
  exact fixedConfiguration_amplitude_eq w
    (bound (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) 0) hcut B V R
    (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) 0) rfl

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
