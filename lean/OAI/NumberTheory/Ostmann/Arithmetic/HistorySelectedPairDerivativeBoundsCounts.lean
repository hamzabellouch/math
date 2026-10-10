import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeBoundsNumerics
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeCounts

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedPairDerivativeBounds
open Construction HistoryOccurrenceVariables HistoryPairSmoothXi HistorySymbolicEncoding
open HistorySelectedPairDerivativeCounts

def countConstant (k : ℕ) : ℝ :=
  (2+rootCounterpartDerivativeConstant*(k+1))*(countCoefficient k:ℝ)

lemma countConstant_pos (k : ℕ) : 0 < countConstant k := by
  have hc : 0 < (countCoefficient k:ℝ) := by exact_mod_cast countCoefficient_pos k
  unfold countConstant
  positivity [rootCounterpartDerivativeConstant_pos]

lemma two_count_le (k : ℕ) : 2*(countCoefficient k:ℝ) ≤ countConstant k := by
  unfold countConstant
  have hc : 0 ≤ (countCoefficient k:ℝ) := Nat.cast_nonneg _
  have hd : 0 ≤ rootCounterpartDerivativeConstant*(k+1) := by
    positivity [rootCounterpartDerivativeConstant_pos]
  nlinarith

theorem actual_pair_card_bound {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hl : l ≤ k)
    {m : ℝ} (hb : (b:ℝ) ≤ m) :
    (Fintype.card (Key h):ℝ)+Fintype.card (Key g) ≤ countConstant k*(m+1) := by
  calc
    _ ≤ 2*(countCoefficient k:ℝ)*(b+1) := pair_key_sum_le_real hh hg hl
    _ ≤ countConstant k*(b+1) :=
      mul_le_mul_of_nonneg_right (two_count_le k) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (countConstant_pos k).le

theorem actual_counterpart_count_bound {b k l cellCount : ℕ} (h : History l) {g : History l}
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hl : l ≤ k) (j : ℕ)
    (hc : cellCount ≤ (k+1)*countCoefficient k*(b+1))
    {m : ℝ} (hb : (b:ℝ) ≤ m) :
    ((pairedDiagonalHKeys h g j).length:ℝ)+(pairedDiagonalUKeys h g j).length+
      rootCounterpartDerivativeConstant*cellCount ≤ countConstant k*(m+1) := by
  have hH : ((pairedDiagonalHKeys h g j).length:ℝ) ≤ (countCoefficient k:ℝ)*(b+1) := by
    exact_mod_cast pairedDiagonalHKeys_length_le h hg hl j
  have hU : ((pairedDiagonalUKeys h g j).length:ℝ) ≤ (countCoefficient k:ℝ)*(b+1) := by
    exact_mod_cast pairedDiagonalUKeys_length_le h hg hl j
  have hC : (cellCount:ℝ) ≤ (k+1)*(countCoefficient k:ℝ)*(b+1) := by exact_mod_cast hc
  have hR := mul_le_mul_of_nonneg_left hC rootCounterpartDerivativeConstant_pos.le
  calc
    _ ≤ countConstant k*(b+1) := by unfold countConstant; nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (countConstant_pos k).le

end Ostmann.Arithmetic.HistorySelectedPairDerivativeBounds

end

end OAI
