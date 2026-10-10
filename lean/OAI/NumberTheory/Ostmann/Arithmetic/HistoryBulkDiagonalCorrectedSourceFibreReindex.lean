import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReferenceDisintegration
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMeanEnergySum

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkDiagonalCorrectedSourceFibreReindex
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryGiantOriginalMeanFactorization (Current Choices choicesPairSum)
open HistoryBulkIndependentFibreReference (RemainingPermutation)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

def guardedFibreMean (outside : List ℕ) (a : SelectedNonbulkSample C l)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) (c₁ c₂ : Choices (l:=l) C) : ℂ :=
  if PreservesRemainingBands (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))) e then
    HistoryBulkIndependentFibreReference.mixedFibreMean C outside a e v.val v.val c₁ c₂
  else 0

theorem guardedMean_disintegration (outside : List ℕ)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) (c₁ c₂ : Choices (l:=l) C) :
    (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).cmean (fun x =>
      HistoryDiagonalCorrectedOriginalMean.guardedOriginalMixedMean C outside x e v c₁ c₂) =
    (selectedNonbulkPrior C l).cmean (fun a => guardedFibreMean C outside a e v c₁ c₂) := by
  by_cases hb : PreservesRemainingBands (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))) e
  · simp only [HistoryDiagonalCorrectedOriginalMean.guardedOriginalMixedMean,guardedFibreMean,ite_eq_left hb]
    exact HistoryBulkIndependentFibreReference.sourceMean_disintegration C outside e v.val v.val c₁ c₂
  · simp only [HistoryDiagonalCorrectedOriginalMean.guardedOriginalMixedMean,guardedFibreMean,ite_eq_right hb,
      FinitePrior.cmean, mul_zero, Finset.sum_const_zero]

def correctedFibreMeanComplex (spectator : PrimeSource)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) : ℂ :=
  (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds =>
    (selectedNonbulkPrior C l).cmean (fun a =>
      ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
        choicesPairSum C (fun c₁ c₂ => guardedFibreMean C (spectatorList spectator ds) a e v c₁ c₂)))

theorem selectedDiagonalCovariance_eq_fibres (spectator : PrimeSource)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) :
    C.selectedDiagonalCovariance spectator (bulkSize k L/2) C.scale l e =
      correctedFibreMeanComplex (l:=l) C spectator e := by
  rw [HistoryDiagonalCorrectedOriginalMean.selectedDiagonalCovariance_eq_originalMean]
  unfold correctedFibreMeanComplex
  apply congrArg (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
  funext ds
  simp only [choicesPairSum,FinitePrior.cmean_sum,FinitePrior.cmean_mul_left]
  simp_rw [guardedMean_disintegration C]

end Ostmann.Arithmetic.HistoryBulkDiagonalCorrectedSourceFibreReindex

end

end OAI
