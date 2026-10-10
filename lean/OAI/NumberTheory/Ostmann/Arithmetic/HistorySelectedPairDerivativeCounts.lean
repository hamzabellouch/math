import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCounterpartBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeCountsBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedPairDerivativeCounts
open Construction HistoryOccurrenceVariables HistorySymbolicEncoding HistoryPairPattern
open HistoryPairSmoothXi HistoryProductWindows

theorem diagonal_prior_cells_card_le {b k l : ℕ} {g : History l}
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k)
    (j : ℕ) (giants : List Bool) (hgiants : giants.length ≤ 2) :
    (Finset.univ : Finset (Fin (diagonalCellKeys g j).length ⊕ Fin giants.length)).card ≤
      countCoefficient k*(b+1) := by
  simpa only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin] using
    (Nat.add_le_add_left hgiants (diagonalCellKeys g j).length).trans
      (diagonalCellKeys_length_add_two_le hg hlk j)

theorem diagonal_prime_cells_card_le {b k l : ℕ} {g : History l}
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) (j : ℕ) :
    (Finset.univ : Finset (Fin (diagonalCellKeys g j).length ⊕
      Fin ([false,true] : List Bool).length)).card ≤ countCoefficient k*(b+1) :=
  diagonal_prior_cells_card_le hg hlk j _ (by simp)

theorem diagonal_mixed_cells_card_le {b k l : ℕ} {g : History l}
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) (j : ℕ) :
    (Finset.univ : Finset (Fin (diagonalCellKeys g j).length ⊕
      Fin ([true] : List Bool).length)).card ≤ countCoefficient k*(b+1) :=
  diagonal_prior_cells_card_le hg hlk j _ (by simp)

theorem diagonal_cells_card_le {b k l : ℕ} {g : History l}
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) (j : ℕ) :
    (Finset.univ : Finset (Fin (diagonalCellKeys g j).length)).card ≤
      countCoefficient k*(b+1) := by
  have h := diagonalCellKeys_length_add_two_le hg hlk j
  simpa only [Finset.card_univ, Fintype.card_fin] using (by omega :
    (diagonalCellKeys g j).length ≤ countCoefficient k*(b+1))

theorem all_level_cells_add_two_le {b k l : ℕ} {g : History l}
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) :
    (∑ j : Fin (l+1), (diagonalCellKeys g j.val).length)+2 ≤
      (k+1)*countCoefficient k*(b+1) := by
  have hs : (∑ j : Fin (l+1), ((diagonalCellKeys g j.val).length+2)) ≤
      (l+1)*(countCoefficient k*(b+1)) := by
    calc
      _ ≤ ∑ _j : Fin (l+1), countCoefficient k*(b+1) :=
        Finset.sum_le_sum (fun j _ => diagonalCellKeys_length_add_two_le hg hlk j.val)
      _ = _ := by simp
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hs
  have hm := Nat.mul_le_mul_right (countCoefficient k*(b+1)) (Nat.add_le_add_right hlk 1)
  calc
    _ ≤ (l+1)*(countCoefficient k*(b+1)) := by omega
    _ ≤ (k+1)*(countCoefficient k*(b+1)) := hm
    _ = _ := by ring

theorem pair_key_sum_le_real {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) :
    (Fintype.card (Key h) : ℝ)+Fintype.card (Key g) ≤
      2*(countCoefficient k : ℝ)*(b+1) := by
  exact_mod_cast pair_key_sum_le hh hg hlk

theorem counterpartWidths_le {k l : ℕ} (hlk : l ≤ k) :
    (nominalInheritedWidth k l+2)+nominalRemovedWidth k l ≤
      3+(2:ℝ)^k*(18+10*(k:ℝ)) := by
  rw [HistoryGiantCounterpartBounds.counterpartWidths_sum]
  have hp : (2:ℝ)^l ≤ 2^k := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) hlk
  gcongr

theorem counterpartWidths_le_linear (b : ℕ) {k l : ℕ} (hlk : l ≤ k) :
    (nominalInheritedWidth k l+2)+nominalRemovedWidth k l ≤
      (3+(2:ℝ)^k*(18+10*(k:ℝ)))*(b+1) := by
  apply (counterpartWidths_le hlk).trans
  have hb : (1:ℝ) ≤ b+1 := by
    have : (0:ℝ) ≤ b := Nat.cast_nonneg b
    linarith
  exact le_mul_of_one_le_right (by positivity) hb

end Ostmann.Arithmetic.HistorySelectedPairDerivativeCounts

end

end OAI
