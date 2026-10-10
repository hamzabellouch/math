import OAI.NumberTheory.Ostmann.Arithmetic.GiantCollisionError
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackground
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGoodPatternAggregation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation
open HistoryBulkActualPrincipalBlockFamily HistoryBulkGoodPatternAggregation
open HistoryBulkUniversalPatternAggregation Filter
attribute [local instance] Classical.propDecidable
local instance actualGoodMeanInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def backgroundMean (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
    (families : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      OriginalOuter (fun _ : Bool=>C.giant) C.sources
        (Template.initial (2*(bulkSize k L/2)) k) l p → Family C outside l p)
    (corrected mixed : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  (backgroundPrior C l).cmean (fun bg=>
    patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
      (fun p b=>familyValue (families p (restoreOuterBackground C l p bg b)) b corrected mixed hV))

theorem backgroundMean_eq_original (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
    (families : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      OriginalOuter (fun _ : Bool=>C.giant) C.sources
        (Template.initial (2*(bulkSize k L/2)) k) l p → Family C outside l p)
    (corrected mixed : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    backgroundMean C outside families corrected mixed hV=
      ∑p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
        ∑o,(outerMass C l p o:ℂ)*(∏q : Block p,((outerBlocks C l p o q).val:ℂ))*
          (if Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q)) then
            familyValue (families p o) (outerBlocks C l p o) corrected mixed hV else 0) := by
  symm
  simpa only [backgroundMean,outerBlocks_restoreOuterBackground] using
    outer_pattern_sum_eq_background_cmean C l
      (fun p o=>familyValue (families p o) (outerBlocks C l p o) corrected mixed hV)

theorem exists_backgroundMean_budget (d : Decomposition) (Bs BD Bz H : ℝ)
    (hBs : 0 ≤ Bs) {k : ℕ} (hk : 2 ≤ k) (hH : 0 ≤ H) :
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
        OriginalOuter (fun _ : Bool=>C.giant) C.sources
          (Template.initial (2*(bulkSize k L/2)) k) l p → Family C (spectatorList spectator ds) l p)
        (corrected mixed : Bool), (corrected=true → l<k) →
      ‖backgroundMean C (spectatorList spectator ds) families corrected mixed hV‖ ≤
        Real.exp (-H*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  obtain ⟨ε,hε,hbound⟩ := exists_complete_good_pattern_budget d Bs BD Bz H hBs hk hH
  refine ⟨ε,hε,?_⟩
  filter_upwards [hbound] with L hL
  intro spectator hband hflat ds E C hG hGu hc hcu hb hd l hl
  obtain ⟨hV,hB⟩ := hL spectator hband hflat ds E C hG hGu hc hcu hb hd l hl
  refine ⟨hV,?_⟩
  intro families corrected mixed hstage
  apply GiantCollisionError.norm_cmean_le_of_mass_ne_zero
  intro bg _
  exact hB (fun p b=>families p (restoreOuterBackground C l p bg b)) corrected mixed hstage

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
