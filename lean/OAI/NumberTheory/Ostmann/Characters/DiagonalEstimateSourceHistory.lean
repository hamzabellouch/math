import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceDefs
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateUnitHistory
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalExpectations

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget InitialCharacterScale HigherBiasSourceRoleBounds
attribute [local instance] Classical.propDecidable

theorem real_mean_sum_re_mul {I J : Type*} [Fintype I] (ν : FinitePrior I)
    (R : Finset J) (C : ℝ) (F : I → J → ℂ) :
    ν.mean (fun y=>∑P∈R,((C:ℂ)*F y P).re) =
      C*(∑P∈R,ν.cmean (fun y=>F y P)).re := by
  have h : (ν.cmean (fun y=>∑P∈R,(C:ℂ)*F y P)).re =
      ν.mean (fun y=>∑P∈R,((C:ℂ)*F y P).re) := by
    simp only [prior_cmean_re,Complex.re_sum]
  rw [←h]
  simp_rw [←Finset.mul_sum]
  rw [FinitePrior.cmean_mul_left,FinitePrior.cmean_sum]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j<k) (B V : (l:ℕ) → State k (l+1) → ℤ)

abbrev SourceHistory :=
  SupportedHistory (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) j []

def sourceHistoryPairMean (P : ℕ+)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (h h' : SourceHistory (k:=k) (L:=L) (BD:=BD) j) : ℂ :=
  (outsidePrimePrior (schedule k j) j (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledShells w j) (sourceScheduledShells_pos w j)).cmean (fun y=>
      normalizedHistoryPair
        (fun i=>sourceScheduledShells w j
          (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) i))
        (fun _=>sourceScheduledShells_pos w j _)
        (historyRootIndex j (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) [])
        (unitHistoryTerm k j hj (sourceWidth w.configuration (wordSize k L))
          (sourceScheduledUnits w j) (sourceScheduledCharacters w j) (sourceScheduledCenters w j)
          B V (canonicalHistoryExtra k (sourcePivotRanges w))
          (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
            (initialGap BD k L) (configurationProductWidth k c)))
          s.locations.X (initialGap BD k L) (configurationProductWidth k c)
          (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) [] y P)
        (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j)
        (gapSchedule BD k L (j+1)) e h h')

theorem sourceMatchingAverage_eq_normalized_history
    (A : Finset (Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))) :
    sourceMatchingAverage w j hj B V A =
      (copiedNormalization (actualCopiedShells w.configuration (wordSize k L) j
        (s.locations.base 0) (s.locations.base 2) s.locations.primes)*
        Real.exp (-sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j-
          gapSchedule BD k L (j+1)))*
      (∑P∈sourcePivotRanges w j,∑e∈A,
        ∑h:SourceHistory (k:=k) (L:=L) (BD:=BD) j,
        ∑h':SourceHistory (k:=k) (L:=L) (BD:=BD) j,sourceHistoryPairMean w j hj B V P e h h').re := by
  unfold sourceMatchingAverage unitMatchingAverage
  simp_rw [unitRootContribution_eq_normalized_history k j hj
    (sourceWidth w.configuration (wordSize k L))
    (sourceScheduledUnits w j) (sourceScheduledCharacters w j) (sourceScheduledCenters w j)
    B V (canonicalHistoryExtra k (sourcePivotRanges w))
    (canonicalHistoryMask k (sourceRangeLeafMask k s.J s.locations.X
      (initialGap BD k L) (configurationProductWidth k c)))
    s.locations.X (initialGap BD k L) (configurationProductWidth k c)
    (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) []
    _ _ (sourceScheduledShells w j) (sourceScheduledShells_pos w j) A
    (sourcePivotTarget w.configuration s.J (gapSchedule BD k L) j)
    (gapSchedule BD k L (j+1))]
  rw [real_mean_sum_re_mul]
  simp_rw [FinitePrior.cmean_sum]
  rfl

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI
