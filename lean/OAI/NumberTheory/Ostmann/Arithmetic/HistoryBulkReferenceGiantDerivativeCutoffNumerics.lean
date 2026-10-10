import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightDerivConstants

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative
open HistorySelectedPairDerivativeBounds

def cutoffCost : ℝ := 2*partitionDerivativeConstant+1

lemma cutoffCost_pos : 0 < cutoffCost := by
  unfold cutoffCost
  linarith [partitionDerivativeConstant_pos]

def cutoffExponent (Bs BD Bz : ℝ) (k : ℕ) : ℝ :=
  selectedExponent Bs BD Bz k+cutoffCost

lemma cutoffExponent_pos (Bs BD Bz : ℝ) (k : ℕ) : 0 < cutoffExponent Bs BD Bz k :=
  add_pos (selectedExponent_pos Bs BD Bz k) cutoffCost_pos

lemma cutoffCost_mul_exp_le (C : ℝ) (m : ℕ) :
    cutoffCost*Real.exp (C*((m:ℝ)+1)) ≤
      Real.exp ((C+cutoffCost)*((m:ℝ)+1)) := by
  have he : cutoffCost ≤ Real.exp cutoffCost := by
    linarith [Real.add_one_le_exp cutoffCost]
  calc
    _ ≤ Real.exp cutoffCost*Real.exp (C*((m:ℝ)+1)) :=
      mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
    _ = Real.exp (cutoffCost+C*((m:ℝ)+1)) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg cutoffCost_pos.le (Nat.cast_nonneg m (α:=ℝ))]

lemma exp_le_cutoff_exp (C : ℝ) (m : ℕ) :
    Real.exp (C*((m:ℝ)+1)) ≤ Real.exp ((C+cutoffCost)*((m:ℝ)+1)) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right cutoffCost_pos.le) (by positivity)

end Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative

end

end OAI
