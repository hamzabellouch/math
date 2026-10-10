import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateHistoryRatioBasic
import OAI.NumberTheory.Ostmann.Construction.JoinedRemaining

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds
open TemplateOneSidedSupportTelescoping
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k) (B V : (l:ℕ) → State k (l+1) → ℤ)

theorem copiedWindowRatio_mul_sourceHistoryTerm (hc : 0 < c)
    (y : OutsideConstituent (schedule k j) j (sourceWidth w.configuration (wordSize k L)) →
      PrimeUpTo s.locations.Q) (P : ℕ+)
    (f : ActualCopied w.configuration (wordSize k L) j → PrimeUpTo s.locations.Q)
    (h : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
    (hf : (copiedPrimePrior (schedule k j) j (sourceWidth w.configuration (wordSize k L))
      (sourceScheduledShells w j) (sourceScheduledShells_pos w j)).mass f ≠ 0) :
    copiedWindowRatio
      (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+gapSchedule BD k L (j+1))
      (sourceCopiedWidth k c) ((∏i,(f i).val:ℕ):ℤ)*sourceHistoryTerm w j hj B V y P f h =
      ((Real.exp (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+
        gapSchedule BD k L (j+1))/((∏i,(f i).val:ℕ):ℝ):ℝ):ℂ)*
      sourceHistoryTerm w j hj B V y P f h := by
  by_cases ht : sourceHistoryTerm w j hj B V y P f h=0
  · simp only [ht,mul_zero]
  · rw [copiedWindowRatio_eq_of_sourceHistoryTerm_ne_zero w j hj B V hc y P f h hf ht]

def cutoffSourceHistoryPairMean (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) : ℂ :=
  (outsidePrimePrior (schedule k j) j (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledShells w j) (sourceScheduledShells_pos w j)).cmean (fun y=>
    (copiedPrimePrior (schedule k j) j (sourceWidth w.configuration (wordSize k L))
      (sourceScheduledShells w j) (sourceScheduledShells_pos w j)).cmean (fun f=>
      copiedWindowRatio
        (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j+gapSchedule BD k L (j+1))
        (sourceCopiedWidth k c) ((∏i,(f i).val:ℕ):ℤ)*
      ((∏i,if f (e i)∈sourceScheduledShells w j
        (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) i)
        then (1:ℝ) else 0):ℂ)*
      (if historyRootIndex j (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) [] h'=
        historyRootIndex j (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) [] h
      then sourceHistoryTerm w j hj B V y P f h*
        conj (sourceHistoryTerm w j hj B V y P (f∘e) h') else 0)))

theorem sourceHistoryPairMean_eq_cutoff (hc : 0 < c) (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) :
    sourceHistoryPairMean w j hj B V P e h h'=
      cutoffSourceHistoryPairMean w j hj B V P e h h' := by
  unfold sourceHistoryPairMean normalizedHistoryPair cutoffSourceHistoryPairMean
  apply congrArg (FinitePrior.cmean _)
  funext y
  apply FinitePrior.cmean_congr_support
  intro f hf
  by_cases ht : sourceHistoryTerm w j hj B V y P f h=0
  · change _* (if _ then sourceHistoryTerm w j hj B V y P f h*_ else 0) =
      _*(if _ then sourceHistoryTerm w j hj B V y P f h*_ else 0)
    simp only [ht,zero_mul,ite_self,mul_zero]
  · rw [copiedWindowRatio_eq_of_sourceHistoryTerm_ne_zero w j hj B V hc y P f h hf ht]
    simp only [Complex.ofReal_mul,Complex.ofReal_prod]
    congr 2
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> rfl

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
