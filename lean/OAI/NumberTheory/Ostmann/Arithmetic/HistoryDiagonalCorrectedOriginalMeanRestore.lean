import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMeanDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMean
open Construction Conclusion HistorySignedXiTransport HistoryGiantReferenceMean
open HistoryGiantOriginalMeanFactorization hiding originalMixedMean
open HistoryDiagonalSmallOriginalMean hiding originalMixedMean
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
variable (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))

theorem originalMixedMean_eq_remaining (outside : List ℕ)
    (v w : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
    (c e : Choices (l:=l) C) :
    originalMixedMean C outside x y v.val w.val c e =
      ∑ p ∈ integerPivotCell C.giantCenter, (externalPivotWeight C.giantCenter p:ℂ) *
        C.giant.law.cmean (fun q =>
          (diagonalSmallTerm d C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L)
            C.giant outside l p (outerAssignment C x) ((q,smallAssignment C x),v):ℂ) *
          (remainingCounterpart C.sources (Current (k:=k) (L:=L) (l:=l)) (l+1) C.giant
            ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k L l)
            (C.compensationLogScale l) C.giantCenter (C.cells.center (bulkSize k L/2))
            (outerAssignment C y) (q,smallAssignment C y):ℂ) *
          supportedHistoryPairXi d (frequencyBound Bs BD Bz k L) outside
            (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter
            (decodeHistory C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l
              (remainingState C.sources (Current (k:=k) (L:=L) (l:=l)) (l+1) C.giant p
                (outerAssignment C x) (q,smallAssignment C x) v.val) c)
            (decodeHistory C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l
              (remainingState C.sources (Current (k:=k) (L:=L) (l:=l)) (l+1) C.giant p
                (outerAssignment C y) (q,smallAssignment C y) w.val) e)) := by
  unfold originalMixedMean mixedMean sourceIntegrand
  simp_rw [smallMultiplier_nat_eq_diagonalSmallTerm C x outside,
    giant_sourceState_eq_remainingState C x, giant_sourceState_eq_remainingState C y,
    counterpart_nat_eq_remainingCounterpart C y]

end Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMean

end

end OAI
