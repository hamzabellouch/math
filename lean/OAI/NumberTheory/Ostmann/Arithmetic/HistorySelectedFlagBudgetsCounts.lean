import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairFlags
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPairDerivativeCounts

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedFlagBudgets
open Construction HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairRows HistoryPairRepresentatives HistoryPairFlags
open HistorySelectedPairDerivativeCounts

theorem degreeBudget_le {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) :
    degreeBudget h g ≤ 2*historyCostCoefficient k*(b+1) := by
  have h₁ := hh.cost_le hlk
  have h₂ := hg.cost_le hlk
  unfold degreeBudget
  nlinarith

theorem polynomial_degree_le {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside) (gs : g.Supported V outside)
    (r : Representative h g) (i : Index h g r) :
    (polynomial h g hs gs r i).totalDegree ≤ 8*historyCostCoefficient k*(b+1) := by
  exact (polynomial_degree h g hs gs r i).trans (by
    have hd := degreeBudget_le hh hg hlk
    nlinarith)

theorem occurrences_card_le {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) :
    Fintype.card (Occurrences h g) ≤ 2*countCoefficient k*(b+1) := by
  have hc := pair_key_sum_le hh hg hlk
  simp only [key_card] at hc
  simp only [Occurrences,Fintype.card_sum,internalKey_card]
  omega

theorem fiber_card_le {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k)
    (r : Representative h g) :
    Fintype.card (Fiber h g r) ≤ 2*countCoefficient k*(b+1) := by
  apply (Fintype.card_le_of_injective (fun i : Fiber h g r => i.val)
    Subtype.val_injective).trans
  exact occurrences_card_le hh hg hlk

theorem index_card_le {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k)
    (r : Representative h g) :
    Fintype.card (Index h g r) ≤
      2*(2*countCoefficient k*(b+1))+(2*countCoefficient k*(b+1))^2 := by
  rw [index_card]
  have hf := fiber_card_le hh hg hlk r
  have hs := Nat.mul_le_mul hf hf
  simp only [pow_two]
  exact Nat.add_le_add (Nat.mul_le_mul_left 2 hf) hs

theorem representative_card_le {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) :
    Fintype.card (Representative h g) ≤ 2*countCoefficient k*(b+1) :=
  (Fintype.card_le_of_surjective (label h g) (label_surjective h g)).trans
    (occurrences_card_le hh hg hlk)

theorem degreeBudget_le_real {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) :
    (degreeBudget h g:ℝ) ≤ 2*(historyCostCoefficient k:ℝ)*(b+1) := by
  exact_mod_cast degreeBudget_le hh hg hlk

theorem polynomial_degree_le_real {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside) (gs : g.Supported V outside)
    (r : Representative h g) (i : Index h g r) :
    ((polynomial h g hs gs r i).totalDegree:ℝ) ≤ 8*(historyCostCoefficient k:ℝ)*(b+1) := by
  exact_mod_cast polynomial_degree_le hh hg hlk hs gs r i

theorem occurrences_card_le_real {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) :
    (Fintype.card (Occurrences h g):ℝ) ≤ 2*(countCoefficient k:ℝ)*(b+1) := by
  exact_mod_cast occurrences_card_le hh hg hlk

theorem fiber_card_le_real {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k)
    (r : Representative h g) :
    (Fintype.card (Fiber h g r):ℝ) ≤ 2*(countCoefficient k:ℝ)*(b+1) := by
  exact_mod_cast fiber_card_le hh hg hlk r

theorem index_card_le_real {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k)
    (r : Representative h g) :
    (Fintype.card (Index h g r):ℝ) ≤
      2*(2*(countCoefficient k:ℝ)*(b+1))+(2*(countCoefficient k:ℝ)*(b+1))^2 := by
  exact_mod_cast index_card_le hh hg hlk r

theorem representative_card_le_real {b k l : ℕ} {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hlk : l ≤ k) :
    (Fintype.card (Representative h g):ℝ) ≤ 2*(countCoefficient k:ℝ)*(b+1) := by
  exact_mod_cast representative_card_le hh hg hlk

end Ostmann.Arithmetic.HistorySelectedFlagBudgets

end

end OAI
