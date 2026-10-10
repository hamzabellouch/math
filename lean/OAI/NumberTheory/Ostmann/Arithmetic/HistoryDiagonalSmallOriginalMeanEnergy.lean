import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMeanEnergyFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMeanRestore
import OAI.NumberTheory.Ostmann.Construction.DiagonalSingleHistoryComplex

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMean
open Construction Conclusion
open HistoryGiantOriginalMeanFactorization hiding originalMixedMean
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem diagonalSingleXiPairComplex_eq_originalMean
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (m : ℕ) (c e : Choices (l:=l) C) :
    diagonalSingleXiPairComplex d C.sources (Seed (k:=k) (L:=L))
      (frequencyBound Bs BD Bz k L) C.giant spectator m
      (bulkSize k L/2) (bulkSize k L/2) C.scale C.giantCenter C.bulkBin C.spectatorBin l c e =
    ((choicesMass C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l c *
      choicesMass C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l e : ℝ) : ℂ) *
      (spectatorPrior spectator m).cmean (fun ds =>
        (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).cmean (fun x =>
          ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
            originalMixedMean C (spectatorList spectator ds) x x v.val v.val c e)) := by
  unfold diagonalSingleXiPairComplex
  rw [← FinitePrior.cmean_mul_left]
  apply congrArg (FinitePrior.cmean (spectatorPrior spectator m))
  funext ds
  let A (u : SourceAssignment C.sources (Template.extracted (l+1) (Current (k:=k) (L:=L) (l:=l))))
      (p : ℕ) (q : C.giant.Sample)
      (x : SourceAssignment C.sources (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))))
      (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) : ℂ :=
    (diagonalSmallTerm d C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L)
      C.giant (spectatorList spectator ds) l p u ((q,x),v) : ℂ)
  let B (u : SourceAssignment C.sources (Template.extracted (l+1) (Current (k:=k) (L:=L) (l:=l))))
      (p : ℕ) (q : C.giant.Sample)
      (x : SourceAssignment C.sources (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))))
      (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) : ℂ :=
    supportedHistoryPairXi d (frequencyBound Bs BD Bz k L) (spectatorList spectator ds)
      (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter
      (decodeHistory C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l
        (remainingState C.sources (Current (k:=k) (L:=L) (l:=l)) (l+1) C.giant p u (q,x) v.val) c)
      (decodeHistory C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l
        (remainingState C.sources (Current (k:=k) (L:=L) (l:=l)) (l+1) C.giant p u (q,x) v.val) e)
  have hr :
      (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).cmean (fun x =>
        ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
          originalMixedMean C (spectatorList spectator ds) x x v.val v.val c e) =
      (assignmentPrior C.sources (Template.extracted (l+1) (Current (k:=k) (L:=L) (l:=l)))).cmean (fun u =>
        (assignmentPrior C.sources (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l)))).cmean (fun x =>
          ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
            ∑ p ∈ integerPivotCell C.giantCenter, (externalPivotWeight C.giantCenter p : ℂ) *
              C.giant.law.cmean (fun q => A u p q x v * B u p q x v))) := by
    simp_rw [originalMixedMean_eq_remaining]
    exact restoringAssignment_cmean C.sources (l+1) (Current (k:=k) (L:=L) (l:=l))
      (fun ux => ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
        ∑ p ∈ integerPivotCell C.giantCenter, (externalPivotWeight C.giantCenter p : ℂ) *
          C.giant.law.cmean (fun q => A ux.1 p q ux.2 v * B ux.1 p q ux.2 v))
  rw [hr, ← FinitePrior.cmean_mul_left]
  apply congrArg (FinitePrior.cmean
    (assignmentPrior C.sources (Template.extracted (l+1) (Current (k:=k) (L:=L) (l:=l)))))
  funext u
  exact weighted_pair_frequency_cmean_factor C.giant.law
    (assignmentPrior C.sources (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))))
    (integerPivotCell C.giantCenter) (fun p => (externalPivotWeight C.giantCenter p : ℂ))
    (((choicesMass C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l c *
      choicesMass C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l e : ℝ) : ℂ))
    (A u) (B u)

end Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMean

end

end OAI
