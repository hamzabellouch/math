import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMeanEnergyBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMeanRestore
import OAI.NumberTheory.Ostmann.Construction.DiagonalHistoryXi

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMean
open Construction Conclusion
open HistoryGiantOriginalMeanFactorization hiding originalMixedMean
open HistoryDiagonalSmallOriginalMean hiding originalMixedMean originalMixedMean_eq_remaining
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
local notation "T" => Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))

def guardedOriginalMixedMean (outside : List ℕ)
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (e : Equiv.Perm (RemainingIndex T))
    (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) (c₁ c₂ : Choices (l:=l) C) : ℂ :=
  if PreservesRemainingBands T e then
    if hc : SmallCounterpartCompatible C.sources T (smallAssignment C x) e then
      originalMixedMean C outside x (counterpartCurrentAssignment C x e hc) v.val v.val c₁ c₂
    else 0
  else 0

theorem guardedOriginalMixedMean_eq_remaining (outside : List ℕ)
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (e : Equiv.Perm (RemainingIndex T))
    (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) (c₁ c₂ : Choices (l:=l) C) :
    guardedOriginalMixedMean C outside x e v c₁ c₂ =
      ∑ p ∈ integerPivotCell C.giantCenter, (externalPivotWeight C.giantCenter p : ℂ) *
        C.giant.law.cmean (fun q =>
          (diagonalSmallTerm d C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L)
            C.giant outside l p (outerAssignment C x) ((q,smallAssignment C x),v) : ℂ) *
          C.diagonalPairXiTerm (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L)
            (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin outside l
            (C.compensationLogScale l) (stepGap BD Bz k L l) p (outerAssignment C x)
            (q,smallAssignment C x) v c₁ c₂ e) := by
  unfold guardedOriginalMixedMean
  by_cases hb : PreservesRemainingBands T e
  · rw [ite_eq_left hb]
    by_cases hc : SmallCounterpartCompatible C.sources T (smallAssignment C x) e
    · rw [dite_eq_left hc, originalMixedMean_eq_remaining]
      simp only [counterpartCurrentAssignment_outer, counterpartCurrentAssignment_small]
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      apply congrArg (FinitePrior.cmean C.giant.law)
      funext q
      have hq := (counterpartCompatible_iff_small C.sources T C.giant q
        (smallAssignment C x) e hb).mpr hc
      simp only [InitialSourceChoice.diagonalPairXiTerm, dite_eq_left hq, ite_eq_left hb,
        reconstructCounterpart_eq_small C.sources T C.giant q (smallAssignment C x) e hb hq]
      ac_rfl
    · rw [dite_eq_right hc]
      have hn : ∀ q : C.giant.Sample,
          ¬ CounterpartCompatible C.sources T C.giant (q,smallAssignment C x) e := by
        intro q hq
        exact hc ((counterpartCompatible_iff_small C.sources T C.giant q
          (smallAssignment C x) e hb).mp hq)
      simp only [InitialSourceChoice.diagonalPairXiTerm, dite_eq_right (hn _), mul_zero,
        FinitePrior.cmean, Finset.sum_const_zero]
  · rw [ite_eq_right hb]
    have hz : ∀ p (q : C.giant.Sample),
        C.diagonalPairXiTerm (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L)
          (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin outside l
          (C.compensationLogScale l) (stepGap BD Bz k L l) p (outerAssignment C x)
          (q,smallAssignment C x) v c₁ c₂ e = 0 := by
      intro p q
      unfold InitialSourceChoice.diagonalPairXiTerm
      split_ifs <;> simp_all
    simp only [hz, mul_zero, FinitePrior.cmean, Finset.sum_const_zero]

end Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMean

end

end OAI
