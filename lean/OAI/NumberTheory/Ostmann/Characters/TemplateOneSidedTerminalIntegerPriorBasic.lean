import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateIntegerPrior
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalPriorMean

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval
open Construction Preliminaries Template Template.OneSidedPhase TemplateSupportRemoval
open HigherBiasSource HigherBiasSource.SourceTemplate InitialCharacterScale DiagonalEstimate
open HistoryFrequencyLabels HistoryFrequencyBudget ParityActions
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ)

abbrev terminalSourceIndex :=
  (schedule k (n+1)).Constituent (sourceWidth w.configuration (wordSize k L))

def terminalSourceIntegerSupport (i : terminalSourceIndex w n) : Finset ℤ :=
  integerPrimeSupport (sourceScheduledShells w (n+1) i)

def terminalSourceIntegerWeight (i : terminalSourceIndex w n) (a : ℤ) : ℝ :=
  integerPrimeWeight (sourceScheduledShells w (n+1) i) a

def terminalSourceNaturalSupport (i : terminalSourceIndex w n) : Finset ℕ :=
  (sourceScheduledShells w (n+1) i).image (fun p=>p.val)

theorem terminalSourceIntegerWeight_cast (i : terminalSourceIndex w n)
    (p : PrimeUpTo s.locations.Q) :
    terminalSourceIntegerWeight w n i (p.val:ℤ)=(sourceTerminalCoordinatePrior w n i).mass p :=
  integerPrimeWeight_cast _ (sourceScheduledShells_pos w (n+1) i) p

theorem terminalSourcePrior_cmean_integer (G : (terminalSourceIndex w n → ℤ) → ℂ) :
    (productPrior (sourceTerminalCoordinatePrior w n)).cmean
      (fun p=>G (primeIntegerAssignment p)) =
      fullProductMean (terminalSourceIntegerSupport w n) (terminalSourceIntegerWeight w n) G :=
  primeProductPrior_cmean_eq_integer _ (sourceScheduledShells_pos w (n+1)) G

theorem terminalSourcePrior_cmean_eq_integer
    (F : (terminalSourceIndex w n → PrimeUpTo s.locations.Q) → ℂ) :
    (productPrior (sourceTerminalCoordinatePrior w n)).cmean F =
      fullProductMean (terminalSourceIntegerSupport w n) (terminalSourceIntegerWeight w n)
        (integerPrimeTest F) :=
  primeProductPrior_cmean_eq_integer_extended _ (sourceScheduledShells_pos w (n+1)) F

theorem terminalSource_support_exists_prime (x : terminalSourceIndex w n → ℤ)
    (hx : ∀i,x i∈terminalSourceIntegerSupport w n i) :
    ∃p : terminalSourceIndex w n → PrimeUpTo s.locations.Q,
      (∀i,p i∈sourceScheduledShells w (n+1) i) ∧ primeIntegerAssignment p=x := by
  have hh : ∀i,∃p : PrimeUpTo s.locations.Q,
      p∈sourceScheduledShells w (n+1) i ∧ (p.val:ℤ)=x i := by
    intro i
    exact Finset.mem_image.mp (hx i)
  choose p hp he using hh
  exact ⟨p,hp,funext he⟩

theorem terminal_sourceHistoryPairMean_eq_integer
    (B V : (l:ℕ)→State k (l+1)→ℤ)
    (σ τ : Reassignments k n (wordSize k L))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) (n+1)) (hroot : h.val.1=h'.val.1) :
    SourceTemplate.sourceHistoryPairMean w B V n σ τ h h' =
      fullProductMean (terminalSourceIntegerSupport w n) (terminalSourceIntegerWeight w n)
        (integerPrimeTest (sourceTerminalKernel w n B V σ τ h h')) := by
  rw [terminal_sourceHistoryPairMean_eq_cmean w B V n σ τ h h' hroot,
    terminalSourcePrior_cmean_eq_integer]

end
end Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval

end

end OAI
