import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMeanEnergyTerms
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMeanEnergyFinite
import OAI.NumberTheory.Ostmann.Construction.DiagonalHistoryCovariance

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMean
open Construction Conclusion
open HistoryGiantOriginalMeanFactorization hiding originalMixedMean
open HistoryDiagonalSmallOriginalMean hiding originalMixedMean originalMixedMean_eq_remaining
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
local notation "T" => Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))
local notation "U" => Template.extracted (l+1) (Current (k:=k) (L:=L) (l:=l))

theorem correctedHistoryPairExpression_eq_cmean_Xi (outside : List ℕ) (p : ℕ)
    (u : SourceAssignment C.sources U) (c₁ c₂ : Choices (l:=l) C)
    (e : Equiv.Perm (RemainingIndex T)) :
    C.correctedHistoryPairExpression (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L)
      C.scale (sourceStateBins (bulkSize k L/2) (bulkSize k L/2) C.bulkBin C.spectatorBin)
      outside l (C.compensationLogScale l) (stepGap BD Bz k L l) p u c₁ c₂ e =
    (remainingPrior C.sources T C.giant).cmean (fun x =>
      ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
        (diagonalSmallTerm d C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L)
          C.giant outside l p u (x,v) : ℂ) *
        (((choicesMass C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l c₁ *
          choicesMass C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l c₂ : ℝ) : ℂ) *
          C.diagonalPairXiTerm (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L)
            (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin outside l
            (C.compensationLogScale l) (stepGap BD Bz k L l) p u x v c₁ c₂ e)) := by
  rw [C.correctedHistoryPairExpression_eq_Xi]
  simp only [FinitePrior.cmean, Finset.mul_sum, mul_assoc]

theorem diagonalHistoryCovariance_eq_originalMean (spectator : PrimeSource) (m : ℕ)
    (c₁ c₂ : Choices (l:=l) C) (e : Equiv.Perm (RemainingIndex T)) :
    C.diagonalHistoryCovariance (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L)
      spectator m C.scale
      (sourceStateBins (bulkSize k L/2) (bulkSize k L/2) C.bulkBin C.spectatorBin)
      l (C.compensationLogScale l) (stepGap BD Bz k L l) c₁ c₂ e =
    ((choicesMass C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l c₁ *
      choicesMass C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l c₂ : ℝ) : ℂ) *
      (spectatorPrior spectator m).cmean (fun ds =>
        (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).cmean (fun x =>
          ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
            guardedOriginalMixedMean C (spectatorList spectator ds) x e v c₁ c₂)) := by
  unfold InitialSourceChoice.diagonalHistoryCovariance
  simp_rw [correctedHistoryPairExpression_eq_cmean_Xi]
  rw [← FinitePrior.cmean_mul_left]
  apply congrArg (FinitePrior.cmean (spectatorPrior spectator m))
  funext ds
  let A (u : SourceAssignment C.sources U) (p : ℕ) (q : C.giant.Sample)
      (x : SourceAssignment C.sources T)
      (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) : ℂ :=
    (diagonalSmallTerm d C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L)
      C.giant (spectatorList spectator ds) l p u ((q,x),v) : ℂ)
  let B (u : SourceAssignment C.sources U) (p : ℕ) (q : C.giant.Sample)
      (x : SourceAssignment C.sources T)
      (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) : ℂ :=
    C.diagonalPairXiTerm (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L)
      (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin
      (spectatorList spectator ds) l (C.compensationLogScale l) (stepGap BD Bz k L l)
      p u (q,x) v c₁ c₂ e
  have hr :
      (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).cmean (fun x =>
        ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
          guardedOriginalMixedMean C (spectatorList spectator ds) x e v c₁ c₂) =
      (assignmentPrior C.sources U).cmean (fun u =>
        (assignmentPrior C.sources T).cmean (fun x =>
          ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
            ∑ p ∈ integerPivotCell C.giantCenter, (externalPivotWeight C.giantCenter p : ℂ) *
              C.giant.law.cmean (fun q => A u p q x v * B u p q x v))) := by
    simp_rw [guardedOriginalMixedMean_eq_remaining]
    exact restoringAssignment_cmean C.sources (l+1) (Current (k:=k) (L:=L) (l:=l))
      (fun ux => ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
        ∑ p ∈ integerPivotCell C.giantCenter, (externalPivotWeight C.giantCenter p : ℂ) *
          C.giant.law.cmean (fun q => A ux.1 p q ux.2 v * B ux.1 p q ux.2 v))
  rw [hr, ← FinitePrior.cmean_mul_left]
  apply congrArg (FinitePrior.cmean (assignmentPrior C.sources U))
  funext u
  exact weighted_pair_frequency_cmean_factor C.giant.law (assignmentPrior C.sources T)
    (integerPivotCell C.giantCenter) (fun p => (externalPivotWeight C.giantCenter p : ℂ))
    (((choicesMass C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l c₁ *
      choicesMass C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l c₂ : ℝ) : ℂ))
    (A u) (B u)

end Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMean

end

end OAI
