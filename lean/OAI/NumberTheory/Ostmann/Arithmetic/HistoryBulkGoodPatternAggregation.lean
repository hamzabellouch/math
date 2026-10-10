import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGoodPatternAggregationFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGoodPatternPrincipalFrame

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGoodPatternAggregation
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryBulkGoodPatternPrincipalFrame
open HistoryBulkUniversalPatternAggregation HistoryRepresentativeSourceSeparation Filter
open scoped BigOperators
local instance goodSelectedInternalDecidable (template : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal template l) := Classical.decEq _

theorem exists_complete_good_pattern_budget
    (d : Decomposition) (Bs BD Bz H : ℝ) (hBs : 0 ≤ Bs) {k : ℕ} (hk : 2 ≤ k)
    (hH : 0 ≤ H) :
    ∃ ε : ℝ,0 < ε ∧ ∀ᶠ L : ℝ in atTop,∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℕ) ∧
        Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      (∀p : spectator.Sample,(FiniteField.correlationBound (residueTransform d p.val):ℝ) ≤ ε) →
      ∀ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
      ∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀l : ℕ,l ≤ k →
      ∃hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q,
      ∀(families : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
        (Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) →
        Family C (spectatorList spectator ds) l p)
        (corrected mixed : Bool), (corrected=true → l<k) →
      ‖patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        (fun p b=>familyValue (families p b) b corrected mixed hV)‖ ≤
        Real.exp (-H*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  have hk' : 0 < k := by omega
  obtain ⟨ε,hε,hPaid⟩ := exists_principalOperator_budget d Bs BD Bz H hBs hk' hH
  refine ⟨ε,hε,?_⟩
  filter_upwards [hPaid,selected_patternComplexSum_eventually d Bs BD Bz hk,
    SourceFrequencyBounds.frequency_lt_of_log_lower_eventually Bs BD Bz hk'
      (by norm_num : (0:ℝ)<1/2000)] with L hPaid hPattern hFreq
  intro spectator hband hflat ds E C hG hGu hc hcu hb hd l hl
  have hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q := by
    intro q hq j hj
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hq
    have hlog := (hband (ds i)).1
    rw [hi] at hlog
    have hp : q.Prime := by
      rw [←hi]
      exact spectator.prime _ (ds i).property
    exact hFreq j (hj.trans hl) q hp.pos hlog
  refine ⟨hV,?_⟩
  intro families corrected mixed hstage
  calc
    _ ≤ (Real.exp (-H*(2:ℝ)^l*(bulkSize k L:ℝ)) /
        Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ))) *
        Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
      apply hPattern E C hG hGu hc hcu hb hd l hl
      · exact div_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
      · intro p b _ _
        apply familyValue_norm_le_of_paid _ _ _ _ _ _ (Real.exp_nonneg _)
        intro i r _
        exact hPaid spectator hband hflat ds E C hG hc hcu hb hd l hl
          r.frame corrected mixed r.permutation hV hstage r.good
    _ = _ := div_mul_cancel₀ _ (Real.exp_ne_zero _)

end Ostmann.Arithmetic.HistoryBulkGoodPatternAggregation

end

end OAI
