import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterEquiv

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation
open HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryBulkActualPrincipalBlockFamily
attribute [local instance] Classical.propDecidable
local instance correctedMeanMassInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))

theorem originalDrawMass_restore_ne_zero
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (u : SelectedBulkSample C l)
    (ho : outerMass C l p o≠0) (hu : (selectedBulkPrior C l).mass u≠0) :
    originalDrawMass (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p (restoreOriginalDraw C l p o u)≠0 := by
  rw [originalDrawMass_restore C l p o u]
  exact mul_ne_zero ho hu

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
