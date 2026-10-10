import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalBound
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalSamples

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistorySelectedPairDerivativeBounds Filter
attribute [local instance] Classical.propDecidable
local instance principalFinalInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_principal_pattern_frequency_error_eventually (d : Decomposition)
    (Bs BD Bz : ℝ) {k : ℕ} (hBs : 0 ≤ Bs) (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀l (corrected mixed : Bool),(if corrected then l<k else l≤k) →
      ∀outside : List ℕ,(∀p∈outside,0<p) → outside.length ≤ bulkSize k L →
      (∀p∈outside,Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀F : (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l) →
        (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
        PrincipalBlockFamily C outside l f g p,
      (∑f,∑g,∑p,4*(F f g p).mean corrected mixed) ≤ Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
  filter_upwards [selected_active_pattern_frequency_error_eventually d Bs BD Bz
      (selectedExponent Bs BD Bz k+64) hk,
    selected_principal_family_weightBound_eventually d Bs BD Bz hBs hk] with L hsum hweight
  intro E C hG hGu hc hcu hb hd l corrected mixed hl outside hpos hlen hlog F
  have hl' : l≤k := by
    cases corrected with
    | false => exact hl
    | true => exact Nat.le_of_lt hl
  exact hsum E C hG hGu hc hcu hb hd l hl' outside hpos hlen hlog
    (fun f g p=>(F f g p).toActive corrected mixed)
    (selectedAmplitude (selectedExponent Bs BD Bz k+64) k L l outside)
    (selectedAmplitude_nonneg _ _ _ _ _) (le_refl _)
    (fun f g p=>hweight E C hG hc outside l corrected mixed hl f g p (F f g p))

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
