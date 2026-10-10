import OAI.NumberTheory.Ostmann.Conclusion.LowLevelBadPairs
import OAI.NumberTheory.Ostmann.Construction.DiagonalPermutationCount
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalEnvironment

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction
namespace InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem correctedCounterpartTerm_zero_of_not_bands (C : InitialSourceChoice d Bs BD Bz k L E)
    (seed : List SourceSlot) (l : ℕ) (B Δ : ℝ)
    (u : SourceAssignment C.sources (Template.extracted (l+1) (Template.current seed l)))
    (x : RemainingSample C.sources (Template.remainder (l+1) (Template.current seed l)) C.giant)
    (F : RemainingSample C.sources (Template.remainder (l+1) (Template.current seed l)) C.giant→ℂ)
    (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Template.current seed l))))
    (he : ¬PreservesRemainingBands (Template.remainder (l+1) (Template.current seed l)) e) :
    C.correctedCounterpartTerm seed l B Δ u x F e=0 := by
  unfold correctedCounterpartTerm
  split_ifs <;> simp_all

theorem diagonalCovariance_zero_of_not_bands (C : InitialSourceChoice d Bs BD Bz k L E)
    (seed : List SourceSlot) (V : ℕ→ℕ) (spectator : PrimeSource) (m : ℕ) (X : ℝ)
    (bins : List ℕ→State→ℝ) (l : ℕ) (B Δ : ℝ)
    (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Template.current seed l))))
    (he : ¬PreservesRemainingBands (Template.remainder (l+1) (Template.current seed l)) e) :
    C.diagonalCovariance seed V spectator m X bins l B Δ e=0 := by
  unfold diagonalCovariance correctedSmallCounterpartExpression FinitePrior.cmean
  simp only [C.correctedCounterpartTerm_zero_of_not_bands seed l B Δ _ _ _ e he,
    map_zero,mul_zero,Finset.sum_const_zero]

theorem selectedDiagonalCovariance_zero_of_not_bands (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s : ℕ) (X : ℝ) (l : ℕ)
    (e : Equiv.Perm (RemainingIndex
      (Template.remainder (l+1) (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l))))
    (he : ¬PreservesRemainingBands
      (Template.remainder (l+1) (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)) e) :
    C.selectedDiagonalCovariance spectator s X l e=0 :=
  C.diagonalCovariance_zero_of_not_bands _ _ _ _ _ _ _ _ _ _ he

def diagonalBadPermutation (m k l : ℕ)
    (e : Equiv.Perm (RemainingIndex (DiagonalPermutationCount.remainingTemplate m k l))) : Prop :=
  PreservesRemainingBands (DiagonalPermutationCount.remainingTemplate m k l) e ∧
    Conclusion.TransferBadArrangement (DiagonalPermutationCount.remainingBulkPermutation m k l e)

def diagonalGoodPermutation (m k l : ℕ)
    (e : Equiv.Perm (RemainingIndex (DiagonalPermutationCount.remainingTemplate m k l))) : Prop :=
  PreservesRemainingBands (DiagonalPermutationCount.remainingTemplate m k l) e ∧
    ¬Conclusion.TransferBadArrangement (DiagonalPermutationCount.remainingBulkPermutation m k l e)

def selectedBadCovarianceSum (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s : ℕ) (X : ℝ) (l : ℕ) : ℂ :=
  ∑e,if diagonalBadPermutation (2*(Conclusion.bulkSize k L/2)) k l e then
    C.selectedDiagonalCovariance spectator s X l e else 0

def selectedGoodCovarianceSum (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s : ℕ) (X : ℝ) (l : ℕ) : ℂ :=
  ∑e,if diagonalGoodPermutation (2*(Conclusion.bulkSize k L/2)) k l e then
    C.selectedDiagonalCovariance spectator s X l e else 0

theorem selectedDiagonalCovariance_sum_split (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (s : ℕ) (X : ℝ) (l : ℕ) :
    (∑e,C.selectedDiagonalCovariance spectator s X l e)=
      C.selectedBadCovarianceSum spectator s X l+C.selectedGoodCovarianceSum spectator s X l := by
  unfold selectedBadCovarianceSum selectedGoodCovarianceSum
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hb : PreservesRemainingBands
      (DiagonalPermutationCount.remainingTemplate (2*(Conclusion.bulkSize k L/2)) k l) e
  · by_cases hbad : Conclusion.TransferBadArrangement
        (DiagonalPermutationCount.remainingBulkPermutation (2*(Conclusion.bulkSize k L/2)) k l e)
    · simp only [diagonalBadPermutation,diagonalGoodPermutation,hb,hbad,true_and,not_true_eq_false,
        ite_true,ite_false,add_zero]
    · simp only [diagonalBadPermutation,diagonalGoodPermutation,hb,hbad,true_and,not_false_eq_true,
        ite_true,ite_false,zero_add]
  · rw [C.selectedDiagonalCovariance_zero_of_not_bands spectator s X l e hb]
    simp only [diagonalBadPermutation,diagonalGoodPermutation,hb,false_and,ite_false,add_zero]

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
