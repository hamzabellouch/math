import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalBulkSamples
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagPrincipalFamily

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryBulkReplacementGeometry HistoryBulkSpectatorReferenceRaw
attribute [local instance] Classical.propDecidable
local instance principalSamplesInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ} {l : ℕ}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {R : BlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) outside l p}

theorem PrincipalReferenceData.amplitude_residue_eq_sourceBulkUnits (P : PrincipalReferenceData C R)
    (y : OriginalDraw (fun _ : Bool=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p) :
    (P.amplitude (originalDrawBulk C l p y)).residue=
      sourceBulkUnits (bulkModulus R.left.history R.right.history outside P.K) C.sources
        (2*(bulkSize k L/2)) k l (originalDrawAssignment C l p y) := by
  exact (sourceBulkUnits_originalDrawAssignment C l p y
    (bulkModulus R.left.history R.right.history outside P.K)).symm

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
