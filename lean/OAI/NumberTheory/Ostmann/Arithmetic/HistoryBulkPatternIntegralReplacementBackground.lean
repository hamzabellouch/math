import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackground
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacement
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns Filter
open HistoryPairSourceLaws HistoryBulkUniversalPatternAggregation HistoryBulkActualPrincipalBlockFamily
open scoped BigOperators
local instance bulkBackgroundInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}

def backgroundValue (after : Bool)
    (F : Background C l → ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) →
        Family C outside l p)
    (corrected mixed : Bool)
    (hV : ∀q∈outside,∀j ≤ l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  (backgroundPrior C l).cmean (fun bg=>patternComplexSum C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
    (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
    (fun p b=>familyValue after (F bg p b) b corrected mixed hV))

theorem selected_background_bulk_error_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop,∀spectator : PrimeSource,
      (∀p:spectator.Sample,Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
    ∀ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
    ∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
    ∀l ≤ k,∀(corrected mixed : Bool)
      (hV : ∀q∈spectatorList spectator ds,∀j ≤ l,frequencyBound Bs BD Bz k L j<q),
      (corrected=true → l<k) →
    ∀F : Background C l → ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) →
      Family C (spectatorList spectator ds) l p,
    ‖backgroundValue false F corrected mixed hV-backgroundValue true F corrected mixed hV‖ ≤
        Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖backgroundValue false F corrected mixed hV-backgroundValue true F corrected mixed hV‖ ≤
        Real.exp (-H*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_pattern_bulk_error_eventually d Bs BD Bz H hBs hH hk] with L hL
  intro spectator hspec ds E C hG hGu hcl hcu hb hd l hl corrected mixed hV hstage F
  have h (bg : Background C l) :=
    hL spectator hspec ds E C hG hGu hcl hcu hb hd l hl corrected mixed hV hstage (F bg)
  unfold backgroundValue
  rw [GiantCollisionError.cmean_sub_eq]
  constructor
  · apply GiantCollisionError.norm_cmean_le_of_mass_ne_zero
    intro bg _
    exact (h bg).1
  · apply GiantCollisionError.norm_cmean_le_of_mass_ne_zero
    intro bg _
    exact (h bg).2

end Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacement

end

end OAI
