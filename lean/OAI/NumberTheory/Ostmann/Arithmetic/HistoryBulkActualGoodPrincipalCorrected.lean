import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedPattern
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPatternIntegralReplacementBackground

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryBulkUniversalPatternAggregation Filter
attribute [local instance] Classical.propDecidable
local instance actualGoodCorrectedInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)

def correctedPrincipal (_hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e)
    (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  HistoryBulkPatternIntegralReplacement.backgroundValue true
    (fun bg p b=>correctedFamily C p (restoreOuterBackground C l p bg b)
      (spectatorList spectator ds) e he
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)) true true hV

theorem correctedPrincipal_eq_backgroundMean (hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e)
    (hgood : ¬TransferBadArrangement
      (DiagonalPermutationCount.remainingBulkPermutation (2*(bulkSize k L/2)) k l e))
    (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    correctedPrincipal C spectator ds hl e he hV=
      backgroundMean C (spectatorList spectator ds)
        (fun p o=>correctedGoodFamily C p o (spectatorList spectator ds) e he
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) hgood)
        true true hV := by
  unfold correctedPrincipal HistoryBulkPatternIntegralReplacement.backgroundValue backgroundMean
  apply congrArg ((backgroundPrior C l).cmean)
  funext bg
  apply congrArg (patternComplexSum C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
    (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  funext p b
  exact familyValue_correctedFamily C p _ (spectatorList spectator ds) e he
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) hgood b hV

theorem exists_corrected_principal_budget (d : Decomposition) (Bs BD Bz H : ℝ)
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
      ∀(l : ℕ)(hl : l<k),
      ∃hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q,
      ∀(e : RemainingPermutation (k:=k) (L:=L) (l:=l))
        (he : PreservesRemainingBands _ e),
      ¬TransferBadArrangement
        (DiagonalPermutationCount.remainingBulkPermutation (2*(bulkSize k L/2)) k l e) →
      ‖correctedPrincipal C spectator ds hl e he hV‖ ≤
        Real.exp (-H*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  obtain ⟨ε,hε,hbound⟩ := exists_backgroundMean_budget d Bs BD Bz H hBs hk hH
  refine ⟨ε,hε,?_⟩
  filter_upwards [hbound] with L hL
  intro spectator hband hflat ds E C hG hGu hc hcu hb hd l hl
  obtain ⟨hV,hB⟩ := hL spectator hband hflat ds E C hG hGu hc hcu hb hd l hl.le
  refine ⟨hV,?_⟩
  intro e he hgood
  rw [correctedPrincipal_eq_backgroundMean C spectator ds hl e he hgood hV]
  exact hB (fun p o=>correctedGoodFamily C p o (spectatorList spectator ds) e he
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) hgood)
    true true (fun _=>hl)

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
