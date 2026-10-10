import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedSample
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightCounts

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedPairDerivativeCounts
open Construction HistoryOccurrenceVariables HistorySymbolicEncoding HistoryPairPattern
open HistoryPairSmoothXi

def countCoefficient (k : ℕ) : ℕ := historyCostCoefficient k + 3

theorem countCoefficient_pos (k : ℕ) : 0 < countCoefficient k := by
  unfold countCoefficient
  omega

theorem key_card_le {b k l : ℕ} {h : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h) (hlk : l ≤ k) :
    Fintype.card (Key h) ≤ historyCostCoefficient k*(b+1) := by
  have hp : 0 < (2:ℕ)^l := by positivity
  calc
    Fintype.card (Key h) = 2+h.root.small.length+h.internalOccurrences.length := key_card h
    _ ≤ 2^l*(2+h.root.small.length+2*h.internalOccurrences.length) := by nlinarith
    _ ≤ _ := hh.cost_le hlk

theorem root_length_add_three_le {b k l : ℕ} {h : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h) (hlk : l ≤ k) :
    h.root.small.length+3 ≤ countCoefficient k*(b+1) := by
  have hk := key_card_le hh hlk
  rw [key_card] at hk
  unfold countCoefficient
  nlinarith

theorem key_card_le_countCoefficient {b k l : ℕ} {h : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h) (hlk : l ≤ k) :
    Fintype.card (Key h) ≤ countCoefficient k*(b+1) := by
  exact (key_card_le hh hlk).trans (Nat.mul_le_mul_right _ (by unfold countCoefficient; omega))

theorem pairKey_card_le_sum {l : ℕ} (h g : History l) :
    Fintype.card (PairKey h g) ≤ Fintype.card (Key h)+Fintype.card (Key g) := by
  simpa only [Fintype.card_sum] using
    Fintype.card_le_of_surjective (unionMap h g) (unionMap_surjective h g)

theorem pair_key_sum_le {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) :
    Fintype.card (Key h)+Fintype.card (Key g) ≤ 2*countCoefficient k*(b+1) := by
  have h₁ := key_card_le_countCoefficient hh hlk
  have h₂ := key_card_le_countCoefficient hg hlk
  calc
    _ ≤ countCoefficient k*(b+1)+countCoefficient k*(b+1) := Nat.add_le_add h₁ h₂
    _ = _ := by ring

theorem pairKey_card_le {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) :
    Fintype.card (PairKey h g) ≤ 2*countCoefficient k*(b+1) :=
  (pairKey_card_le_sum h g).trans (pair_key_sum_le hh hg hlk)

theorem active_card_le {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k)
    (I : Finset (PairKey h g)) : I.card ≤ 2*countCoefficient k*(b+1) :=
  (Finset.card_le_univ I).trans (pairKey_card_le hh hg hlk)

theorem diagonalRoleKeys_length_le {l : ℕ} (h : History l) (pred : SmallSlot → Bool) :
    (diagonalRoleKeys h pred).length ≤ h.root.small.length := by
  unfold diagonalRoleKeys
  simpa only [List.length_map, List.length_finRange] using
    List.length_filter_le (fun i => pred (h.root.small.get i)) (List.finRange h.root.small.length)

theorem pairedDiagonalHKeys_length_le {b k l : ℕ} (h : History l) {g : History l}
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) (j : ℕ) :
    (pairedDiagonalHKeys h g j).length ≤ countCoefficient k*(b+1) := by
  rw [pairedDiagonalHKeys_length, diagonalHKeys, List.length_cons]
  have hr := diagonalRoleKeys_length_le g (fun q => decide (q.role≠.compensation j))
  have hc := root_length_add_three_le hg hlk
  omega

theorem pairedDiagonalUKeys_length_le {b k l : ℕ} (h : History l) {g : History l}
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) (j : ℕ) :
    (pairedDiagonalUKeys h g j).length ≤ countCoefficient k*(b+1) := by
  rw [pairedDiagonalUKeys_length, diagonalUKeys]
  have hr := diagonalRoleKeys_length_le g (fun q => decide (q.role=.compensation j))
  have hc := root_length_add_three_le hg hlk
  omega

theorem diagonalCellKeys_length_add_two_le {b k l : ℕ} {g : History l}
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) (j : ℕ) :
    (diagonalCellKeys g j).length+2 ≤ countCoefficient k*(b+1) := by
  rw [diagonalCellKeys, List.length_cons]
  have hr := diagonalRoleKeys_length_le g
    (fun q => decide (q.role≠.compensation j ∧ q.role≠.bulk))
  have hc := root_length_add_three_le hg hlk
  omega

end Ostmann.Arithmetic.HistorySelectedPairDerivativeCounts

end

end OAI
