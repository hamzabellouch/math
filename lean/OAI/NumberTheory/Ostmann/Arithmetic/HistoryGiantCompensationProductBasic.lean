import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationNormalizationBudgetCounts
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesMass
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesValues
import OAI.NumberTheory.Ostmann.Construction.SmoothHistoryFactor

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryGiantCompensationProduct
open Construction Construction.CanonicalOccurrenceTransport HistoryOccurrenceVariables

theorem decoded_compensationProduct_eq_draws
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small) :
    (decodeHistory sources seed V l a c).compensationProduct =
      ∏ i : Internal seed l, (historyDraws sources seed V l c i).val := by
  let h := decodeHistory sources seed V l a c
  let labels := decoded_tree_source_labels sources seed V l a c ha
  calc
    h.compensationProduct = ∏ i : InternalKey h, (internalSlot h i).value :=
      (prod_internalSlot SmallSlot.value h).symm
    _ = ∏ i : Internal seed l, (internalSlot h (internalEquiv seed h labels i)).value :=
      ((internalEquiv seed h labels).prod_comp (fun i => (internalSlot h i).value)).symm
    _ = ∏ i : Internal seed l, (historyDraws sources seed V l c i).val := by
      apply Finset.prod_congr rfl
      intro i _
      exact decoded_internalSlot_eq_historyDraw sources seed V l a c ha i

theorem historyDraw_mass_ne_zero
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (c : HistoryChoices sources seed V l)
    (hc : choicesMass sources seed V l c ≠ 0) (i : Internal seed l) :
    (sources (internalSource seed i).origin).law.mass (historyDraws sources seed V l c i) ≠ 0 := by
  rw [choicesMass_eq_source_product] at hc
  exact Finset.prod_ne_zero_iff.mp hc i (Finset.mem_univ i)

theorem decoded_compensationProduct_le
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hc : choicesMass sources seed V l c ≠ 0) (B : ℝ)
    (hsource : ∀ origin, ∀ p : (sources origin).Sample,
      (sources origin).law.mass p ≠ 0 → (p.val : ℝ) ≤ B) :
    ((decodeHistory sources seed V l a c).compensationProduct : ℝ) ≤
      B ^ Fintype.card (Internal seed l) := by
  rw [decoded_compensationProduct_eq_draws sources seed V l a c ha,Nat.cast_prod]
  calc
    (∏ i : Internal seed l, ((historyDraws sources seed V l c i).val : ℝ)) ≤
        ∏ _i : Internal seed l, B := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Nat.cast_nonneg _
      · intro i _
        exact hsource _ _ (historyDraw_mass_ne_zero sources seed V l c hc i)
    _ = B ^ Fintype.card (Internal seed l) := by simp

theorem decoded_pair_compensationProduct_le
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a b : State) (c e : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hc : choicesMass sources seed V l c ≠ 0) (he : choicesMass sources seed V l e ≠ 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hsource : ∀ origin, ∀ p : (sources origin).Sample,
      (sources origin).law.mass p ≠ 0 → (p.val : ℝ) ≤ B) :
    ((decodeHistory sources seed V l a c).compensationProduct : ℝ) *
      ((decodeHistory sources seed V l b e).compensationProduct : ℝ) ≤
        B ^ Fintype.card (Internal seed l ⊕ Internal seed l) := by
  rw [Fintype.card_sum,pow_add]
  exact mul_le_mul
    (decoded_compensationProduct_le sources seed V l a c ha hc B hsource)
    (decoded_compensationProduct_le sources seed V l b e hb he B hsource)
    (Nat.cast_nonneg _) (pow_nonneg hB _)

theorem decoded_pair_compensationProduct_initial_le
    (sources : SourceFamily) (V : ℕ → ℕ) (m k l : ℕ) (hl : l ≤ k)
    (a b : State) (c e : HistoryChoices sources (Template.initial m k) V l)
    (ha : Template.Matches (Template.current (Template.initial m k) l) a.small)
    (hb : Template.Matches (Template.current (Template.initial m k) l) b.small)
    (hc : choicesMass sources (Template.initial m k) V l c ≠ 0)
    (he : choicesMass sources (Template.initial m k) V l e ≠ 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hsource : ∀ origin, ∀ p : (sources origin).Sample,
      (sources origin).law.mass p ≠ 0 → (p.val : ℝ) ≤ B) :
    ((decodeHistory sources (Template.initial m k) V l a c).compensationProduct : ℝ) *
      ((decodeHistory sources (Template.initial m k) V l b e).compensationProduct : ℝ) ≤
        B ^ (4*l*2^l) := by
  simpa only [HistoryCompensationNormalizationBudget.paired_internal_card m k l hl] using
    decoded_pair_compensationProduct_le sources (Template.initial m k) V l a b c e
      ha hb hc he B hB hsource

end Ostmann.Arithmetic.HistoryGiantCompensationProduct

end

end OAI
