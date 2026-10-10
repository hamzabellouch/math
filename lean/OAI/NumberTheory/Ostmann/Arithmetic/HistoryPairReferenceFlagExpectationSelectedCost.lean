import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPatternFlagErrorActual

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction Conclusion HistoryPairPattern HistoryPairRows HistoryPairFlags
open HistoryPairRepresentatives HistorySelectedFlagMassBounds HistoryUnnormalizedFlagError
open HistorySelectedPatternFlagError

def selectedUnitBudget (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) {l : ℕ} (h g : History l) : ℝ :=
  ∑r : Representative h g,errorBudget 1
    (((2*Fintype.card (Fiber h g r)+(Fintype.card (Fiber h g r))^2:ℕ):ℝ))
    (((4*degreeBudget h g:ℕ):ℝ))
    (max 0 (Real.log (envelope h g (frequencyBound Bs BD Bz k L)
      (HistorySignedResidues.actualFactorCap Bs BD Bz k L)))/Real.log 2)
    (atomCap k L) (massCap k L) (Fintype.card (PairKey h g))

def selectedAmplitude (C : ℝ) (k : ℕ) (L : ℝ) (l : ℕ) (outside : List ℕ) : ℝ :=
  (outside.prod:ℝ)^(2^(l+1))*Real.exp (C*((bulkSize k L:ℝ)+1))

theorem selectedAmplitude_nonneg (C : ℝ) (k : ℕ) (L : ℝ) (l : ℕ) (outside : List ℕ) :
    0 ≤ selectedAmplitude C k L l outside := by unfold selectedAmplitude; positivity

theorem selectedUnitBudget_nonneg (Bs BD Bz : ℝ) (k : ℕ) (L : ℝ) {l : ℕ} (h g : History l) :
    0 ≤ selectedUnitBudget Bs BD Bz k L h g := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Finset.sum_nonneg
  intro r _
  unfold errorBudget atomCap massCap
  positivity

theorem selectedFlagCost_eq_unitBudget (Bs BD Bz C : ℝ) (k : ℕ) (L : ℝ) {l : ℕ}
    (outside : List ℕ) (h g : History l) :
    selectedFlagCost Bs BD Bz (occurrenceCap k:ℝ) C k L outside h g=
      4*selectedAmplitude C k L l outside*selectedUnitBudget Bs BD Bz k L h g := by
  unfold selectedFlagCost selectedUnitBudget selectedAmplitude atomCap massCap
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  unfold errorBudget
  ring

theorem selectedFlagCost_nonneg (Bs BD Bz C : ℝ) (k : ℕ) (L : ℝ) {l : ℕ}
    (outside : List ℕ) (h g : History l) :
    0 ≤ selectedFlagCost Bs BD Bz (occurrenceCap k:ℝ) C k L outside h g := by
  rw [selectedFlagCost_eq_unitBudget]
  exact mul_nonneg (mul_nonneg (by norm_num) (selectedAmplitude_nonneg C k L l outside))
    (selectedUnitBudget_nonneg Bs BD Bz k L h g)

theorem four_mul_unitBudget_le_selectedFlagCost (Bs BD Bz C : ℝ) (k : ℕ) (L : ℝ) {l : ℕ}
    (outside : List ℕ) (h g : History l) {A : ℝ}
    (hA : A ≤ selectedAmplitude C k L l outside) :
    4*(A*selectedUnitBudget Bs BD Bz k L h g) ≤
      selectedFlagCost Bs BD Bz (occurrenceCap k:ℝ) C k L outside h g := by
  rw [selectedFlagCost_eq_unitBudget,←mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num))
    (selectedUnitBudget_nonneg Bs BD Bz k L h g)

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
