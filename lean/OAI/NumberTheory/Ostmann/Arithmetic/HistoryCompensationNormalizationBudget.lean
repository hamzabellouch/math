import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationNormalizationBudgetPriors
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationNormalizationBudgetScales
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationPatternBudgetHistory

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryCompensationNormalizationBudget
open Construction CanonicalOccurrenceTransport CounterpartNormalizationBound
open CompensationEqualityPatterns HistoryCompensationPatternBudget Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

theorem paired_normalization_budget_eventually {k : ℕ} (hk : 0 < k)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ L : ℝ in atTop, ∀m l : ℕ, l ≤ k →
      let N := Fintype.card (Internal (Template.initial m k) l ⊕ Internal (Template.initial m k) l)
      (2:ℝ)^(N*N)*(2:ℝ)^N*(max 1 (Real.exp L))^N ≤
      Real.exp ((8*k/Conclusion.bulkScale k)*(2:ℝ)^l*Conclusion.bulkSize k L+
        ρ*Conclusion.bulkSize k L) := by
  filter_upwards [eventually_pattern_normalization_budget hk hρ] with L hL
  intro m l hl
  dsimp only
  rw [paired_internal_card m k l hl]
  exact hL l hl

theorem paired_normalization_universal_eventually {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀m l : ℕ, l ≤ k →
      let N := Fintype.card (Internal (Template.initial m k) l ⊕ Internal (Template.initial m k) l)
      (2:ℝ)^(N*N)*(2:ℝ)^N*(max 1 (Real.exp L))^N ≤
      Real.exp (2*(2:ℝ)^l*Conclusion.bulkSize k L) := by
  filter_upwards [eventually_pattern_normalization_universal hk] with L hL
  intro m l hl
  dsimp only
  rw [paired_internal_card m k l hl]
  exact hL l hl

theorem selected_pattern_budget_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ L : ℝ in atTop, ∀(E:Finset ℕ)(C:InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀l : ℕ, l ≤ k →
      let seed := Template.initial (2*(Conclusion.bulkSize k L/2)) k
      (∑p:Pattern (pairedHistoryType seed l),(2:ℝ)^Fintype.card (Block p)*
        ∏q:Block p,blockCap p (fun i => C.sourceNormalization (pairedInternalOrigin seed l i)) q) ≤
      Real.exp ((8*k/Conclusion.bulkScale k)*(2:ℝ)^l*Conclusion.bulkSize k L+
        ρ*Conclusion.bulkSize k L) := by
  filter_upwards [paired_sourceNormalization_exp_bound_eventually d Bs BD Bz hk,
    paired_normalization_budget_eventually hk hρ] with L hn hcost
  intro E C hG hGu hcl hcu hb hd l hl
  dsimp only
  have hc := hn E C hG hGu hcl hcu hb hd l
  apply (sum_pattern_cost_le _ _ (by positivity)
    (fun p => prod_blockCap_le_pow p _ (fun i => (hc i).1)
      (le_max_left 1 (Real.exp L)) (fun i => (hc i).2.trans (le_max_right 1 (Real.exp L))))).trans
  exact hcost _ l hl

theorem selected_pattern_universal_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀(E:Finset ℕ)(C:InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀l : ℕ, l ≤ k →
      let seed := Template.initial (2*(Conclusion.bulkSize k L/2)) k
      (∑p:Pattern (pairedHistoryType seed l),(2:ℝ)^Fintype.card (Block p)*
        ∏q:Block p,blockCap p (fun i => C.sourceNormalization (pairedInternalOrigin seed l i)) q) ≤
      Real.exp (2*(2:ℝ)^l*Conclusion.bulkSize k L) := by
  filter_upwards [paired_sourceNormalization_exp_bound_eventually d Bs BD Bz (by omega : 0 < k),
    paired_normalization_universal_eventually hk] with L hn hcost
  intro E C hG hGu hcl hcu hb hd l hl
  dsimp only
  have hc := hn E C hG hGu hcl hcu hb hd l
  apply (sum_pattern_cost_le _ _ (by positivity)
    (fun p => prod_blockCap_le_pow p _ (fun i => (hc i).1)
      (le_max_left 1 (Real.exp L)) (fun i => (hc i).2.trans (le_max_right 1 (Real.exp L))))).trans
  exact hcost _ l hl

end Ostmann.Arithmetic.HistoryCompensationNormalizationBudget

end

end OAI
