import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionAlgebra

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily HistoryBulkReferenceFrequencyFamily
open HistoryBulkFibreGiantErrorAverage HistoryBulkPrincipalSourceReindexWitness
open HistoryBulkActualPrincipalBlockFamily HistoryPairReferenceFlagExpectation
open HistoryBulkActualPrincipalSourceReindexPattern HistoryBulkActualPrincipalSourceReindexCompensation
open HistoryGiantReferenceMean HistoryBulkFibreGiantApproximationReference
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)

variable (spectator : PrimeSource)
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
  (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)

theorem primeOuterPattern_eq_option (D : OuterData C p o) :
    drawPatternValue C spectator (primeSelectedPrincipal C spectator hactual hl σ)
      ds (outerNonbulk C l p o) i p (outerBlocks C l p o) =
      (selectWitness C (spectatorList spectator ds) σ (outerNonbulk C l p o)
        (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
        (fun _ _ _ _=>1) (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
        hactual hl D.nonbulk_pos D.left_mass D.right_mass
        (spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
        (fun r _=>primeDraw_positive C.giant r) i).elim 0
        (fun r=>primeWitnessPrincipal C (spectatorList spectator ds) σ (outerNonbulk C l p o)
          (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
          r D.nonbulk_pos (D.left_mass i) (D.right_mass i)
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)) /
          blockJacobian C p D.blockDraw :=
  @primeSelectedPrincipal_patternValue_eq_option d Bs BD Bz L k l E C spectator hactual hl σ ds
    (outerNonbulk C l p o) p D.blockDraw D.valid D.nonbulk_pos
    (@outerData_left_mass d Bs BD Bz L k l E C p o D i)
    (@outerData_right_mass d Bs BD Bz L k l E C p o D i) i

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
