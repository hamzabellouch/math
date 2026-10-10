import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateHistoryRatio
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateIntegerPrior
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinFullSourceDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template Template.OneSidedPhase TemplateSupportRemoval
open HigherBiasSource HigherBiasSource.SourceTemplate InitialCharacterScale
open HistoryFrequencyLabels HistoryFrequencyBudget TemplateOneSidedSupportTelescoping
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ)

def sourceSurvivorShells : SurvivingPrimeIndex k j
    (sourceWidth w.configuration (wordSize k L)) → Finset (PrimeUpTo s.locations.Q) :=
  Sum.elim
    (fun i=>sourceScheduledShells w j
      (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) i))
    (fun i=>sourceScheduledShells w j
      (outsideConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) i))

theorem sourceSurvivorShells_pos : ∀i,0 < primeShellMass (sourceSurvivorShells w j i) := by
  intro i
  cases i <;> exact sourceScheduledShells_pos w j _

def sourceSurvivorIntegerSupport := fun i=>integerPrimeSupport (sourceSurvivorShells w j i)
def sourceSurvivorIntegerWeight := fun i=>integerPrimeWeight (sourceSurvivorShells w j i)

theorem sourceSurvivorPrior_eq_product : sourceSurvivorPrior w j =
    productPrior (fun i=>primeShellPrior (sourceSurvivorShells w j i) (sourceSurvivorShells_pos w j i)) := by
  unfold sourceSurvivorPrior
  congr 1
  funext i
  cases i <;> rfl

theorem sourceSurvivorPrior_cmean_eq_integer
    (F : (SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q) → ℂ) :
    (sourceSurvivorPrior w j).cmean F =
      fullProductMean (sourceSurvivorIntegerSupport w j) (sourceSurvivorIntegerWeight w j)
        (integerPrimeTest F) := by
  rw [sourceSurvivorPrior_eq_product]
  exact primeProductPrior_cmean_eq_integer_extended _ _ F

variable (hj : j<k) (B V : (l:ℕ) → State k (l+1) → ℤ)

def cutoffSourceSurvivorKernel (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (x : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q) : ℂ :=
  copiedWindowRatio
    (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+gapSchedule BD k L (j+1))
    (sourceCopiedWidth k c) ((∏i,(x (.inl i)).val:ℕ):ℤ)*
  ((∏i,if x (.inl (e i))∈sourceScheduledShells w j
    (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) i)
    then (1:ℝ) else 0):ℂ)*
  (if historyRootIndex j (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) [] h'=
    historyRootIndex j (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) [] h
  then sourceHistoryTerm w j hj B V (fun i=>x (.inr i)) P (fun i=>x (.inl i)) h*
    conj (sourceHistoryTerm w j hj B V (fun i=>x (.inr i)) P (fun i=>x (.inl (e i))) h') else 0)

theorem cutoffSourceHistoryPairMean_eq_survivor (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) :
    cutoffSourceHistoryPairMean w j hj B V P e h h'=
      (sourceSurvivorPrior w j).cmean (cutoffSourceSurvivorKernel w j hj B V P e h h') := by
  rw [sourceSurvivorPrior_cmean]
  rfl

theorem sourceHistoryPairMean_eq_integer (hc : 0 < c) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) :
    sourceHistoryPairMean w j hj B V P e h h'=
      fullProductMean (sourceSurvivorIntegerSupport w j) (sourceSurvivorIntegerWeight w j)
        (integerPrimeTest (cutoffSourceSurvivorKernel w j hj B V P e h h')) := by
  rw [sourceHistoryPairMean_eq_cutoff w j hj B V hc,
    cutoffSourceHistoryPairMean_eq_survivor,sourceSurvivorPrior_cmean_eq_integer]

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
