import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedScaledFlagErrorBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryUnnormalizedFlagError
open Construction Conclusion HistorySymbolicEncoding HistoryPairPattern HistoryPairRows
open HistoryPairFlags HistoryPairRepresentatives Filter

theorem selected_scaled_flag_error_sum_eventually (Bs BD Bz N C : ℝ) (hN : 0 ≤ N)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k, ∀ (h g : History l),
      TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) h →
      TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) g →
      ∀ (outside : List ℕ), (∀p∈outside,0 < p) → outside.length ≤ bulkSize k L →
      (∀p∈outside,Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      4*(∑ r : Representative h g, errorBudget
        ((outside.prod:ℝ)^(2^(l+1))*Real.exp (C*((bulkSize k L:ℝ)+1)))
        (((2*Fintype.card (Fiber h g r)+(Fintype.card (Fiber h g r))^2:ℕ):ℝ))
        (((4*degreeBudget h g:ℕ):ℝ))
        (max 0 (Real.log (envelope h g (frequencyBound Bs BD Bz k L)
          (HistorySignedResidues.actualFactorCap Bs BD Bz k L)))/Real.log 2)
        (Real.exp (N*L-Real.exp ((39/10000:ℝ)*L))) (Real.exp (N*L))
        (Fintype.card (HistoryPairPattern.PairKey h g))) ≤
          Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
  filter_upwards [selected_flag_error_sum_eventually Bs BD Bz N (C+2) hN hk] with L he
  intro l hl h g hh hg outside hpos hlen hlog
  have he' := he l hl h g hh hg outside hpos hlen hlog
  let A := (outside.prod:ℝ)^(2^(l+1))*Real.exp (C*((bulkSize k L:ℝ)+1))
  let A' := (outside.prod:ℝ)^(2^(l+1))*Real.exp ((C+2)*((bulkSize k L:ℝ)+1))
  let J : Representative h g → ℝ := fun r =>
    ((2*Fintype.card (Fiber h g r)+(Fintype.card (Fiber h g r))^2:ℕ):ℝ)
  let D : ℝ := ((4*degreeBudget h g:ℕ):ℝ)
  let H := max 0 (Real.log (envelope h g (frequencyBound Bs BD Bz k L)
    (HistorySignedResidues.actualFactorCap Bs BD Bz k L)))/Real.log 2
  let atom := Real.exp (N*L-Real.exp ((39/10000:ℝ)*L))
  let mass := Real.exp (N*L)
  let n := Fintype.card (HistoryPairPattern.PairKey h g)
  change 4*(∑ r, errorBudget A (J r) D H atom mass n) ≤ _
  change (∑ r, errorBudget A' (J r) D H atom mass n) ≤ _ at he'
  have hAB : 4*A ≤ A' := four_mul_prefactor_le C (bulkSize k L)
    ((outside.prod:ℝ)^(2^(l+1))) (Nat.cast_nonneg _) (by positivity)
  have hH : 0 ≤ H := div_nonneg (le_max_left _ _)
    (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  calc
    _ = ∑ r, errorBudget (4*A) (J r) D H atom mass n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      unfold errorBudget
      ring
    _ ≤ ∑ r, errorBudget A' (J r) D H atom mass n :=
      Finset.sum_le_sum (fun r _ => errorBudget_mono_prefactor hAB (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) hH (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ ≤ _ := he'

end Ostmann.Arithmetic.HistoryUnnormalizedFlagError

end

end OAI
