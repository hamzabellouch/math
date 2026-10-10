import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindexCancellation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindexWitnessBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCompensation
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily HistoryBulkReferenceFrequencyFamily
open HistoryBulkFibreGiantErrorAverage HistoryBulkPrincipalSourceReindexWitness
open HistoryBulkPrincipalSourceReindex HistoryPairSourceLaws
local instance compensationInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
  (hb : ∀j,(expand p b j).val∈(C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l j)).candidates)

theorem pairedChoiceCompensation_eq_blockJacobian
    (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l) :
    (pairedChoiceCompensation C (leftChoices C (leftDraws C p b hb) i)
      (rightChoices C (rightDraws C p b hb) i):ℂ)=blockJacobian C p b := by
  have h := pairedChoiceCompensation_assemble C i.2.1 i.2.2
    (HistoryCompensationRepresentativePatterns.blockSourceDraws C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p b hb)
  change (pairedChoiceCompensation C (leftChoices C (leftDraws C p b hb) i)
      (rightChoices C (rightDraws C p b hb) i):ℂ)=_ at h
  rw [h]
  apply congrArg (occurrenceJacobian C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
  funext j
  apply Subtype.ext
  rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCompensation

end

end OAI
