import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionPrimeDefs

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

theorem primeSelector_map (D : OuterData C p o) (hD : outerData? C p o=some D) :
    (selectWitness C (spectatorList spectator ds) σ (outerNonbulk C l p o)
      (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
      (fun _ _ _ _=>1) (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
      hactual hl D.nonbulk_pos D.left_mass D.right_mass
      (spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
      (fun r _=>primeDraw_positive C.giant r) i).map
      (fun r=>(⟨D,r⟩ : MatchedSelectedOuter C p o (spectatorList spectator ds) σ
        (fun _ _ _ _=>1) (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i)) =
    selectMatchedOuterReference C p o (spectatorList spectator ds) σ (fun _ _ _ _=>1)
      (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i hactual hl
      (spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
      (fun r _=>primeDraw_positive C.giant r) :=
  (selectMatchedOuterReference_eq_map (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz)
    (L:=L) (k:=k) (l:=l) (E:=E) C p o (spectatorList spectator ds) σ (fun _ _ _ _=>1)
    (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i hactual hl
    (spectatorList_source spectator ds) (primeWeight_nonneg C.giant)
    (fun r _=>primeDraw_positive C.giant r) D hD).symm

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
