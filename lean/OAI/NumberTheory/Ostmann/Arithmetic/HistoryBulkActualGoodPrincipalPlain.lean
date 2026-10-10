import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalPlainDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkGoodPatternAggregation HistoryBulkFibreGiantApproximationReference
open HistoryBulkFibreGiantApproximation
open HistoryGiantReferenceMean HistoryBulkFibreGiantErrorAverage HistoryBulkFibreOriginalReference
open HistoryBulkUniversalPatternAggregation
attribute [local instance] Classical.propDecidable
local instance actualGoodPlainInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (mixed : Bool)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _ : Bool=>C.giant) C.sources
    (Template.initial (2*(bulkSize k L/2)) k) l p)

theorem plainPattern_after_eq_good (hgood : ¬TransferBadArrangement σ)
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    HistoryBulkPatternIntegralReplacement.familyValue true
      (plainPatternFamily C spectator ds hactual hl σ mixed p o) b false mixed hV=
      familyValue (plainGoodFamily C spectator ds hactual hl σ mixed p o hgood) b false mixed hV :=
  Bool.rec
    (motive := fun mixed =>
      HistoryBulkPatternIntegralReplacement.familyValue true
        (plainPatternFamily C spectator ds hactual hl σ mixed p o) b false mixed hV=
      familyValue (plainGoodFamily C spectator ds hactual hl σ mixed p o hgood) b false mixed hV)
    (pattern_after_eq_goodFamily (α := PrimeDraw C.giant) (spectator := spectator)
      C p o (spectatorList spectator ds) σ hgood
      (fun (_ : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) _ _ _=>1)
      (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
      hactual hl (spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
      (fun r _=>primeDraw_positive C.giant r)
      (fun r hr=>prime_draw_cells C r (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr)))
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) false b false hV)
    (pattern_after_eq_goodFamily (α := MixedDraw C.giantCenter C.giant) (spectator := spectator)
      C p o (spectatorList spectator ds) σ hgood
      (fun (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))=>
        plainMixedWeight C (spectatorList spectator ds) (outerNonbulk C l p o) i.1.val)
      (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant)
      hactual hl (spectatorList_source spectator ds) (mixedWeight_nonneg C.giantCenter C.giant)
      (fun r _=>mixedDraw_positive C.giantCenter C.giant r)
      (fun r hr=>mixed_draw_cells C r (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr)))
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) true b false hV
)
    mixed

def plainPrincipal
    (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  HistoryBulkPatternIntegralReplacement.backgroundValue true
    (fun bg p b=>plainPatternFamily C spectator ds hactual hl σ mixed p
      (restoreOuterBackground C l p bg b)) false mixed hV

theorem plainPrincipal_eq_backgroundMean (hgood : ¬TransferBadArrangement σ)
    (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    plainPrincipal C spectator ds hactual hl σ mixed hV=
      backgroundMean C (spectatorList spectator ds)
        (fun p o=>plainGoodFamily C spectator ds hactual hl σ mixed p o hgood) false mixed hV :=
  congrArg ((backgroundPrior C l).cmean) (funext fun bg =>
    congrArg (patternComplexSum C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
      (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
      (funext fun p => funext fun b =>
        plainPattern_after_eq_good C spectator ds hactual hl σ mixed p
          (restoreOuterBackground C l p bg b) hgood b hV))

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
