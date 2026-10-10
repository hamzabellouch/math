import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCopiedCodesPermutation

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate TemplateDiagonalMatching
attribute [local instance] Classical.propDecidable

theorem actualCopied_card {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :
    Fintype.card (ActualCopied cfg m j) = 2^j*(m+1) +
      ∑ i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i},
        nonwordWeight cfg m ((schedule k j).role i.val) := by
  let I := {i : (schedule k j).Slot // (schedule k j).IsCopied j i}
  have hc : Fintype.card {i : I // (schedule k j).role i.val = .word} = 2^j :=
    (Fintype.card_congr (copiedWordEquiv k j)).trans (active_word_card k j)
  have hs : (∑ i : I, if (schedule k j).role i.val = .word then m+1 else 0) = 2^j*(m+1) := by
    rw [← sum_subtype_nat_eq_ite (fun i : I => (schedule k j).role i.val = .word)
      (fun _ => m+1)]
    simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,hc]
  change Fintype.card (Σ i : I, Fin (sourceWidth cfg m ((schedule k j).role i.val))) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [←hs,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hw : (schedule k j).role i.val = .word
  · simp only [hw,nonwordWeight,ite_true,sourceWidth_word,add_zero]
  · simp only [hw,nonwordWeight,ite_false,zero_add]

theorem copiedNonbulk_card {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :
    Fintype.card (CopiedNonbulk cfg m j) = 2^j +
      ∑ i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i},
        nonwordWeight cfg m ((schedule k j).role i.val) := by
  have h := Fintype.card_congr (copiedBulkNonbulkEquiv cfg m j)
  rw [actualCopied_card,Fintype.card_sum,Fintype.card_prod,active_word_card,
    Fintype.card_fin,Nat.mul_add,Nat.mul_one] at h
  omega

theorem copiedNonbulk_card_le {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :
    Fintype.card (CopiedNonbulk cfg m j) ≤ 2^j*(1+2*configCellCount cfg) := by
  rw [copiedNonbulk_card,Nat.mul_add,Nat.mul_one]
  exact Nat.add_le_add_left (copied_nonword_weight_le cfg m j) _

end Ostmann.Characters.DiagonalEstimate

end

end OAI
