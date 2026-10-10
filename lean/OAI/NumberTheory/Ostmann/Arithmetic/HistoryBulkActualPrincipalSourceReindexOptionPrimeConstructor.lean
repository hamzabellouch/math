import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMatchedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionAlgebra
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionConstructors

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

theorem prime_constructor_div
    (D : OuterData C p o)
    (r : Witness C (spectatorList spectator ds) σ (outerNonbulk C l p o)
      (leftDraws C p D.blockDraw D.valid) (rightDraws C p D.blockDraw D.valid)
      (fun _ _ _ _=>1) (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i) :
    primeWitnessPrincipal C (spectatorList spectator ds) σ (outerNonbulk C l p o)
      (leftDraws C p D.blockDraw D.valid) (rightDraws C p D.blockDraw D.valid)
      r D.nonbulk_pos (D.left_mass i) (D.right_mass i)
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) /
      blockJacobian C p D.blockDraw =
    (selectedBulkPrior C l).cmean ((⟨D,r⟩ : MatchedSelectedOuter C p o
      (spectatorList spectator ds) σ (fun _ _ _ _=>1) (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i).rawBTerm (l:=l)
      (fun v hv=>prime_draw_cells C v (lt_of_le_of_ne (primeWeight_nonneg C.giant v) (Ne.symm hv)))
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) false false) :=
  @prime_constructor_quotient d Bs BD Bz L k l E C p o D (spectatorList spectator ds) σ i
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) r
    (fun v hv=>prime_draw_cells C v (lt_of_le_of_ne (primeWeight_nonneg C.giant v) (Ne.symm hv)))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
