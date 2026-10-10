import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexPatternBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexPattern
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily HistoryBulkReferenceFrequencyFamily
open HistoryBulkPrincipalSourceReindex HistoryBulkUniversalPatternAggregation
open HistoryBulkFibreGiantErrorAverage
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)

theorem originalSourceAverage_eq_patternMean
    (F : (Fin (2*(bulkSize k L/2))→spectator.Sample) → SelectedNonbulkSample C l →
      Draws C (l:=l) → Draws C (l:=l) → RootFrequencyIndex (frequencyBound Bs BD Bz k L) l → ℂ) :
    originalSourceAverage C spectator F =
      (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds=>
        (selectedNonbulkPrior C l).cmean (fun a=>
          patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
            (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
            (fun p b=>∑i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l,
              drawPatternValue C spectator F ds a i p b))) := by
  unfold originalSourceAverage
  apply congrArg (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
  funext ds
  apply congrArg (selectedNonbulkPrior C l).cmean
  funext a
  rw [internal_cmean_pair C]
  rw [FinitePrior.cmean_sum,patternComplexSum_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact source_cmean_eq_patternComplexSum C.sources _ _ _

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexPattern

end

end OAI
