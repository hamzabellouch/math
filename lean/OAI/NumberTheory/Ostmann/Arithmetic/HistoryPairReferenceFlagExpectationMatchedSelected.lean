import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationMatchedSelectedPerClass

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistorySelectedPatternFlagError Filter
attribute [local instance] Classical.propDecidable
local instance matchedSelectedFinalInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_matched_active_pattern_frequency_error_eventually (d : Decomposition)
    (Bs BD Bz C₀ : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀l,l ≤ k → ∀outside : List ℕ,
      (∀p∈outside,0 < p) → outside.length ≤ bulkSize k L →
      (∀p∈outside,Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀F : (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l) →
        (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
        MatchedActiveBlockFamily (fun _ : Bool=>C.giant) C.sources
          (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) outside l f g p,
      ∀A : ℝ,0 ≤ A → A ≤ selectedAmplitude C₀ k L l outside →
      (∀f g p,(F f g p).WeightBound A) →
      (∑f,∑g,∑p,4*(F f g p).mean) ≤ Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
  filter_upwards [selected_matched_active_family_error_eventually d Bs BD Bz C₀ hk,
    pattern_frequency_error_eventually Bs BD Bz hk] with L hclass hsum
  intro E C hG hGu hc hcu hb hd l hl outside hpos hlen hlog F A hA hAA hw
  exact hsum (2*(bulkSize k L/2)) l hl (fun f g p=>4*(F f g p).mean)
    (fun f g p=>hclass E C hG hGu hc hcu hb hd l hl outside hpos hlen hlog
      f g p (F f g p) A hA hAA (hw f g p))

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
