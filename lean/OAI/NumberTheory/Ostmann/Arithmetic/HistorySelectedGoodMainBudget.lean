import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedGoodMainBudgetBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedGoodMainBudgetSpectator

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedGoodMainBudget
open Construction Conclusion Filter

theorem exists_good_product_budget (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0 ≤ Bs) (hk : 0 < k) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ L : ℝ in atTop,
      ∀ l : ℕ, l ≤ k → ∀ (outside : List ℕ), outside.length = bulkSize k L →
      ∀ c : Fin outside.length → ℝ,
      (∀ i : Fin outside.length, 0 < outside.get i) →
      (∀ i : Fin outside.length, Real.exp (L/2000) ≤ Real.log (outside.get i:ℝ)) →
      (∀ i, 0 ≤ c i) → (∀ i, c i ≤ ε) →
      goodMainPrefactor Bs BD Bz L k l *
        (∏ i, Tree.treeComparisonConstant (l-2)*(c i+(outside.get i:ℝ)^(-(1/4:ℝ)))) ≤
        Real.exp (-H*(bulkSize k L:ℝ)) := by
  obtain ⟨ε, hε, he⟩ := exists_spectator_product_small k (goodMainCost Bs BD Bz k+H)
  refine ⟨ε, hε, ?_⟩
  filter_upwards [he, eventually_goodMainPrefactor_le Bs BD Bz hBs hk] with L hL hpref
  intro l hl outside hlen c hq hlog hc hcε
  have hp := hL l hl (Fin outside.length) (fun i => outside.get i) c hq hlog hc hcε
  simp only [Fintype.card_fin, hlen] at hp
  have hn : 0 ≤ ∏ i, Tree.treeComparisonConstant (l-2)*
      (c i+(outside.get i:ℝ)^(-(1/4:ℝ))) := by
    apply Finset.prod_nonneg
    intro i _
    exact mul_nonneg (Tree.treeComparisonConstant_nonneg _)
      (add_nonneg (hc i) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  calc
    _ ≤ Real.exp (goodMainCost Bs BD Bz k*(bulkSize k L:ℝ))*
        Real.exp (-(goodMainCost Bs BD Bz k+H)*(bulkSize k L:ℝ)) :=
      mul_le_mul (hpref l hl) hp hn (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem exists_good_product_dyadic_budget (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0 ≤ Bs) (hk : 0 < k) (hH : 0 ≤ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ L : ℝ in atTop,
      ∀ l : ℕ, l ≤ k → ∀ (outside : List ℕ), outside.length = bulkSize k L →
      ∀ c : Fin outside.length → ℝ,
      (∀ i : Fin outside.length, 0 < outside.get i) →
      (∀ i : Fin outside.length, Real.exp (L/2000) ≤ Real.log (outside.get i:ℝ)) →
      (∀ i, 0 ≤ c i) → (∀ i, c i ≤ ε) →
      goodMainPrefactor Bs BD Bz L k l *
        (∏ i, Tree.treeComparisonConstant (l-2)*(c i+(outside.get i:ℝ)^(-(1/4:ℝ)))) ≤
        Real.exp (-H*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  obtain ⟨ε, hε, he⟩ := exists_good_product_budget Bs BD Bz (H*(2:ℝ)^k) hBs hk
  refine ⟨ε, hε, he.mono ?_⟩
  intro L hL l hl outside hlen c hq hlog hc hcε
  apply (hL l hl outside hlen c hq hlog hc hcε).trans
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hl) hH)
    (Nat.cast_nonneg (bulkSize k L) (α:=ℝ))
  nlinarith

end Ostmann.Arithmetic.HistorySelectedGoodMainBudget

end

end OAI
