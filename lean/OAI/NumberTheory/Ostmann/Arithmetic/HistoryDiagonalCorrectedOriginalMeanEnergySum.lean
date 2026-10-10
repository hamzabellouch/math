import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMeanEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantOriginalMeanChoicesDefs
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalEnvironment

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMean
open Construction Conclusion
open HistoryGiantOriginalMeanFactorization hiding originalMixedMean

private theorem double_choice_mean {A B I J R : Type*}
    [Fintype A] [Fintype B] [Fintype I] [Fintype J] [Fintype R]
    (μ : FinitePrior A) (ν : FinitePrior B) (w : I → J → ℂ)
    (F : A → B → R → I → J → ℂ) :
    (∑ i, ∑ j, w i j * μ.cmean (fun a => ν.cmean (fun b => ∑ r, F a b r i j))) =
      μ.cmean (fun a => ν.cmean (fun b => ∑ r, ∑ i, ∑ j, w i j * F a b r i j)) := by
  simp_rw [← FinitePrior.cmean_mul_left, ← FinitePrior.cmean_sum]
  apply congrArg μ.cmean
  funext a
  apply congrArg ν.cmean
  funext b
  simp only [Finset.mul_sum]
  calc
    _ = ∑ i, ∑ r, ∑ j, w i j * F a b r i j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem diagonalCovariance_eq_originalMean
    {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource) (m : ℕ)
    (e : Equiv.Perm (RemainingIndex
      (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))))) :
    C.diagonalCovariance (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L)
      spectator m C.scale
      (sourceStateBins (bulkSize k L/2) (bulkSize k L/2) C.bulkBin C.spectatorBin)
      l (C.compensationLogScale l) (stepGap BD Bz k L l) e =
    (spectatorPrior spectator m).cmean (fun ds =>
      (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).cmean (fun x =>
        ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
          choicesPairSum C (fun c₁ c₂ =>
            guardedOriginalMixedMean C (spectatorList spectator ds) x e v c₁ c₂))) := by
  rw [C.diagonalCovariance_eq_history_pairs]
  simp_rw [diagonalHistoryCovariance_eq_originalMean C spectator m]
  exact double_choice_mean (R := AllowedFrequency (frequencyBound Bs BD Bz k L) l)
    (spectatorPrior spectator m)
    (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l)))
    (fun c₁ c₂ : Choices (l:=l) C =>
      ((choicesMass C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l c₁ *
        choicesMass C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l c₂ : ℝ) : ℂ))
    (fun ds x v c₁ c₂ => guardedOriginalMixedMean C (spectatorList spectator ds) x e v c₁ c₂)

theorem selectedDiagonalCovariance_eq_originalMean
    {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (e : Equiv.Perm (RemainingIndex
      (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l))))) :
    C.selectedDiagonalCovariance spectator (bulkSize k L/2) C.scale l e =
    (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds =>
      (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).cmean (fun x =>
        ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
          choicesPairSum C (fun c₁ c₂ =>
            guardedOriginalMixedMean C (spectatorList spectator ds) x e v c₁ c₂))) :=
  diagonalCovariance_eq_originalMean C spectator (2*(bulkSize k L/2)) e

end Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMean

end

end OAI
