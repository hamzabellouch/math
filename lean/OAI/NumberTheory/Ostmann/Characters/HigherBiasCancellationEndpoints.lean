import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateAssembly
import OAI.NumberTheory.Ostmann.Characters.TemplateSourceIterationActual
import OAI.NumberTheory.Ostmann.Characters.TemplateSourceParity

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasContradiction
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale Filter DiagonalEstimate ParityActions
attribute [local instance] Classical.propDecidable

def TerminalCancellation (d : Decomposition) (δ α β ρ γ c₀ c BD : ℝ) (n : ℕ) : Prop :=
  ∃τ αpair : ℝ,0<τ ∧ 0<αpair ∧ ∀ᶠ L : ℝ in atTop,
    ∀E : Finset ℕ,(∀p∈E,p.Prime) →
    (∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L) →
    ∀s : SelectedWordSource d E δ L (n+1) α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
    ∀σ υ : Reassignments (n+1) n (wordSize (n+1) L),σ≠υ → ∀h h',
      ‖SourceTemplate.sourceHistoryPairMean w
        (sourceRecurrenceB w.configuration s.J (gapSchedule BD (n+1) L) c)
        (sourceRecurrenceV BD (n+1) L) n σ υ h h'‖ ≤ Real.exp (-τ*Real.exp (αpair*L))

def DiagonalCancellation (d : Decomposition) (δ α β ρ γ c₀ c BD : ℝ) (k : ℕ) : Prop :=
  ∃Kpair τ αpair : ℝ,0<τ ∧ 0<αpair ∧ ∀ᶠ L : ℝ in atTop,
    ∀E : Finset ℕ,(∀p∈E,p.Prime) →
    (∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L) →
    ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
    ∀j : ℕ,∀hj : j<k,∀P∈DiagonalEstimate.sourcePivotRanges w j,
    ∀e∈Finset.univ\codePreservingMatchings w.configuration (wordSize k L) j,
    ∀h h':SourceHistory (k:=k) (L:=L) (BD:=BD) j,
      ‖DiagonalEstimate.sourceHistoryPairMean w j hj
        (sourceRecurrenceB w.configuration s.J (gapSchedule BD k L) c)
        (sourceRecurrenceV BD k L) P e h h'‖ ≤
          Real.exp (Kpair*L^2-τ*Real.exp (αpair*L))

end Ostmann.Characters.HigherBiasContradiction

end

end OAI
