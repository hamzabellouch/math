import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPatternFlagError
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedScaledFlagError

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedPatternFlagError
open Construction CompensationEqualityPatterns Conclusion HistoryUnnormalizedFlagError
open HistorySymbolicEncoding HistoryPairRows HistoryPairFlags HistoryPairRepresentatives Filter
attribute [local instance] Classical.propDecidable

def selectedFlagCost (Bs BD Bz N C : ℝ) (k : ℕ) (L : ℝ) {l : ℕ}
    (outside : List ℕ) (h g : History l) : ℝ :=
  4*(∑r : Representative h g,errorBudget
    ((outside.prod:ℝ)^(2^(l+1))*Real.exp (C*((bulkSize k L:ℝ)+1)))
    (((2*Fintype.card (Fiber h g r)+(Fintype.card (Fiber h g r))^2:ℕ):ℝ))
    (((4*degreeBudget h g:ℕ):ℝ))
    (max 0 (Real.log (envelope h g (frequencyBound Bs BD Bz k L)
      (HistorySignedResidues.actualFactorCap Bs BD Bz k L)))/Real.log 2)
    (Real.exp (N*L-Real.exp ((39/10000:ℝ)*L))) (Real.exp (N*L))
    (Fintype.card (HistoryPairPattern.PairKey h g)))

theorem selected_pattern_flag_error_eventually (Bs BD Bz N C : ℝ) (hN : 0 ≤ N)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀l ≤ k, ∀outside : List ℕ,
      (∀p∈outside,0<p)  →  outside.length ≤ bulkSize k L  → 
      (∀p∈outside,Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L))  → 
      ∀left right : FrequencyChoices (frequencyBound Bs BD Bz k L) l  → 
        FrequencyChoices (frequencyBound Bs BD Bz k L) l  → 
        Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)  →  History l,
      (∀f g p,TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) (left f g p))  → 
      (∀f g p,TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) (right f g p))  → 
      (∑f,∑g,∑p,selectedFlagCost Bs BD Bz N C k L outside (left f g p) (right f g p)) ≤ 
        Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
  filter_upwards [pattern_frequency_error_eventually Bs BD Bz hk,
    selected_scaled_flag_error_sum_eventually Bs BD Bz N C hN hk] with L hsum hcost
  intro l hl outside hpos hlen hlog left right hleft hright
  apply hsum (2*(bulkSize k L/2)) l hl
  intro f g p
  exact hcost l hl (left f g p) (right f g p) (hleft f g p) (hright f g p)
    outside hpos hlen hlog

end Ostmann.Arithmetic.HistorySelectedPatternFlagError

end

end OAI
