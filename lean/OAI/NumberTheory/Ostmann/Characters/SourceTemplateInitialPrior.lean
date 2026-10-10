import OAI.NumberTheory.Ostmann.Characters.SourceTemplateInitialIntegrand

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HistoryFrequencyLabels HistoryFrequencyBudget
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem source_amplitude_of_phase_support {k Q : ℕ} (cfg : SourceConfiguration k) (m : ℕ)
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
    (hphase : ∀ w : Fin (sourceHalfSize cfg m+sourceHalfSize cfg m) → PrimeUpTo Q,
      Function.Injective w → ∀ s,
      unitHistoryPhase k 0 (sourceWidth cfg m) (sourceUnitData cfg m ζ)
        (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a)
        (sourceSample cfg m w) s PUnit.unit ≠ 0 →
      CurrentAtomSupport k 0 s (constituentSampleState (schedule k 0) (sourceWidth cfg m)
        (sourceSample cfg m w))) :
    unitAmplitude k 0 (sourceWidth cfg m) (sourceUnitData cfg m ζ)
      (sourceCharacterData cfg m χ) (sourceTranslationData cfg m a) B V
      (canonicalHistoryExtra k R) (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ W))
      X Δ W S (sourcePrimeShells cfg m E) (sourcePrimeShells_positive cfg m E hE) =
    initialCharacterAmplitude (characterDoubleShell E) (characterDoubleShell_positive E hE)
      (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase ζ)
      (characterDoubleMask (sourceHalfMask J)) X := by
  unfold unitAmplitude
  rw [← sourceSample_cmean cfg m E hE]
  unfold initialCharacterAmplitude FinitePrior.cmean
  apply Finset.sum_congr rfl
  intro w hw
  dsimp only
  by_cases hsupport : ∀ i,w i∈characterDoubleShell E i
  · rw [source_integrand_of_phase_support cfg m χ a ζ B V R J X Δ W hX V₀ hcut S hS
      w (hwindow w hsupport) (hphase w)]
  · rw [characterTuplePrior_mass_eq_zero (characterDoubleShell E)
      (characterDoubleShell_positive E hE) w hsupport]
    simp only [Complex.ofReal_zero,zero_mul]

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
