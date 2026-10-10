import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMeanEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantOriginalMeanChoicesDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMean
open Construction Conclusion
open HistoryGiantOriginalMeanFactorization hiding originalMixedMean

private theorem double_choice_mean {A B I J R : Type*}
    [Fintype A] [Fintype B] [Fintype I] [Fintype J] [Fintype R]
    (μ : FinitePrior A) (ν : FinitePrior B) (w : I → J → ℂ)
    (F : A → B → R → I → J → ℂ) :
    (∑ i, ∑ j, w i j * μ.cmean (fun a => ν.cmean (fun b => ∑ r, F a b r i j))) =
      μ.cmean (fun a => ν.cmean (fun b => ∑ r, ∑ i, ∑ j, w i j * F a b r i j)) := by
  simp_rw [←FinitePrior.cmean_mul_left,←FinitePrior.cmean_sum]
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

theorem diagonalSingleEnergy_eq_originalMean
    {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource) (m : ℕ) :
    diagonalSingleEnergy d C.sources (Seed (k:=k) (L:=L))
      (frequencyBound Bs BD Bz k L) C.giant spectator m C.scale C.giantCenter
      (sourceStateBins (bulkSize k L/2) (bulkSize k L/2) C.bulkBin C.spectatorBin) l =
    ((spectatorPrior spectator m).cmean (fun ds =>
      (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).cmean (fun x =>
        ∑ v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
          choicesPairSum C (fun c e =>
            originalMixedMean C (spectatorList spectator ds) x x v.val v.val c e)))).re := by
  rw [diagonalSingleEnergy_eq_complex_Xi_pairs d C.sources (Seed (k:=k) (L:=L))
    (frequencyBound Bs BD Bz k L) C.giant spectator m (bulkSize k L/2) (bulkSize k L/2)
    C.scale C.giantCenter C.bulkBin C.spectatorBin l]
  simp_rw [diagonalSingleXiPairComplex_eq_originalMean C spectator m]
  apply congrArg Complex.re
  have he := double_choice_mean (R := AllowedFrequency (frequencyBound Bs BD Bz k L) l)
    (spectatorPrior spectator m)
    (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l)))
    (fun c e : Choices (l:=l) C =>
      ((choicesMass C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l c *
        choicesMass C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l e:ℝ):ℂ))
    (fun ds x v c e => originalMixedMean C (spectatorList spectator ds) x x v.val v.val c e)
  exact he

end Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMean

end

end OAI
