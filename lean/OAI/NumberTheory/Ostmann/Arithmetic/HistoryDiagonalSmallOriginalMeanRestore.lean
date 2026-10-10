import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMeanDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMean
open Construction Conclusion HistorySignedXiTransport HistoryGiantReferenceMean
open HistoryGiantOriginalMeanFactorization hiding originalMixedMean
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
variable (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))

theorem giant_sourceState_eq_remainingState (p : ℕ) (q : C.giant.Sample) (s : ℤ) :
    giantState (sourceState C.sources _ x s) (p:ℤ) (q.val:ℤ) =
      remainingState C.sources (Current (k:=k) (L:=L) (l:=l)) (l+1) C.giant p
        (outerAssignment C x) (q,smallAssignment C x) s := by
  simp only [giantState,sourceState,remainingState,Int.toNat_natCast]
  congr 1
  exact assignedSlots_split_reinsert C.sources (l+1) _ x

theorem smallMultiplier_nat_eq_diagonalSmallTerm (outside : List ℕ)
    (p : ℕ) (q : C.giant.Sample) (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) :
    smallMultiplier C outside x v.val (p:ℤ) (q.val:ℤ) =
      diagonalSmallTerm d C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L)
        C.giant outside l p (outerAssignment C x) ((q,smallAssignment C x),v) := by
  simp only [smallMultiplier,Int.toNat_natCast]
  rfl

theorem originalMixedMean_eq_remaining (outside : List ℕ)
    (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
    (c e : Choices (l:=l) C) :
    originalMixedMean C outside x x v.val v.val c e =
      ∑ p ∈ integerPivotCell C.giantCenter, (externalPivotWeight C.giantCenter p:ℂ) *
        C.giant.law.cmean (fun q =>
          (diagonalSmallTerm d C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L)
            C.giant outside l p (outerAssignment C x) ((q,smallAssignment C x),v):ℂ) *
          supportedHistoryPairXi d (frequencyBound Bs BD Bz k L) outside
            (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter
            (decodeHistory C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l
              (remainingState C.sources (Current (k:=k) (L:=L) (l:=l)) (l+1) C.giant p
                (outerAssignment C x) (q,smallAssignment C x) v.val) c)
            (decodeHistory C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l
              (remainingState C.sources (Current (k:=k) (L:=L) (l:=l)) (l+1) C.giant p
                (outerAssignment C x) (q,smallAssignment C x) v.val) e)) := by
  unfold originalMixedMean mixedMean sourceIntegrand
  simp_rw [smallMultiplier_nat_eq_diagonalSmallTerm C x outside,
    giant_sourceState_eq_remainingState C x]

end Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMean

end

end OAI
