import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationNumerical

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws Filter
open scoped BigOperators
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_complete_symbolic_pattern_sum_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz)
    {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀(outside : List ℕ)(hout : ∀p∈outside,p∈spectator.candidates),
      outside.length=2*(bulkSize k L/2) → ∀l : ℕ,l≤k →
      ∃hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q,
      ∀(families : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
        (Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) →
        SymbolicPatternFamily C outside l p) (mixed : Bool),
      ‖patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        (fun p b=>(families p b).value b mixed (bulkSize k L/2) (fun q hq=>spectator.prime q (hout q hq)) hV)‖ ≤
        Real.exp ((2:ℝ)^l*(initialGap Bs k L+16*(bulkSize k L:ℝ))) := by
  filter_upwards [selected_symbolic_pattern_sum_eventually d Bs BD Bz hBs hBD hBz hk,
    selected_baseMain_aggregation_eventually Bs hk] with L hFamily hNum
  intro E C hG hGu hc hcu hb hd spectator hspec outside hout hlen l hl
  obtain ⟨hV,hMain⟩ := hFamily E C hG hGu hc hcu hb hd spectator hspec
    (bulkSize k L/2) outside hout hlen l hl
  refine ⟨hV,?_⟩
  intro families mixed
  exact (hMain families mixed).trans (hNum l hl outside hlen)

end Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation

end

end OAI
