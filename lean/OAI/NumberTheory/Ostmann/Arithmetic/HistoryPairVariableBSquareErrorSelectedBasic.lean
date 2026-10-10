import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCompensationProductBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSquareProbabilityProduct

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistoryPairPattern
open HistoryPairRows HistoryGiantCompensationProduct

theorem reciprocal_le_exp_neg_of_log_lower {p A : ℝ} (hp : 0 < p)
    (hlog : A ≤ Real.log p) : 1/p ≤ Real.exp (-A) := by
  calc
    1/p = Real.exp (-Real.log p) := by rw [Real.exp_neg,Real.exp_log hp,one_div]
    _ ≤ Real.exp (-A) := Real.exp_le_exp.mpr (neg_le_neg hlog)

theorem decoded_reciprocal_sum_eq_draws
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small) :
    (∑i : InternalKey (decodeHistory sources seed V l a c),
      (1:ℝ)/(internalSlot (decodeHistory sources seed V l a c) i).value) =
      ∑i : Internal seed l,(1:ℝ)/(historyDraws sources seed V l c i).val := by
  let h := decodeHistory sources seed V l a c
  let labels := decoded_tree_source_labels sources seed V l a c ha
  calc
    _ = ∑i : Internal seed l,(1:ℝ)/(internalSlot h (internalEquiv seed h labels i)).value :=
      ((internalEquiv seed h labels).sum_comp (fun i => (1:ℝ)/(internalSlot h i).value)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [decoded_internalSlot_eq_historyDraw sources seed V l a c ha i]

theorem decoded_pair_reciprocal_sum_le
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a b : State) (c e : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hc : choicesMass sources seed V l c ≠ 0) (he : choicesMass sources seed V l e ≠ 0)
    (B : ℝ) (hsource : ∀origin,∀p:(sources origin).Sample,
      (sources origin).law.mass p ≠ 0 → (1:ℝ)/(p.val:ℝ) ≤ B) :
    (∑i : Occurrences (decodeHistory sources seed V l a c) (decodeHistory sources seed V l b e),
      (1:ℝ)/(slot (decodeHistory sources seed V l a c) (decodeHistory sources seed V l b e) i).value) ≤
      (Fintype.card (Internal seed l⊕Internal seed l):ℝ)*B := by
  change (∑i : InternalKey (decodeHistory sources seed V l a c)⊕InternalKey (decodeHistory sources seed V l b e),
    (1:ℝ)/(Sum.elim (internalSlot (decodeHistory sources seed V l a c))
      (internalSlot (decodeHistory sources seed V l b e)) i).value) ≤ _
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  rw [decoded_reciprocal_sum_eq_draws sources seed V l a c ha,
    decoded_reciprocal_sum_eq_draws sources seed V l b e hb]
  calc
    _ ≤ (∑_i : Internal seed l,B)+(∑_i : Internal seed l,B) := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun i _ => hsource _ _ (historyDraw_mass_ne_zero sources seed V l c hc i))
      · exact Finset.sum_le_sum (fun i _ => hsource _ _ (historyDraw_mass_ne_zero sources seed V l e he i))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_sum,Nat.cast_add,add_mul]

theorem paired_initial_occurrence_count_le (m k l : ℕ) (hl : l ≤ k) :
    Fintype.card (Internal (Template.initial m k) l⊕Internal (Template.initial m k) l) ≤ 4*k*2^k := by
  rw [HistoryCompensationNormalizationBudget.paired_internal_card m k l hl]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hl)
    (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) hl)

end Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected

end

end OAI
