import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportDecoded
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSelectedReference

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation.BlockReference
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryCompensationRepresentativePatterns HistoryPairBulkTransport
attribute [local instance] Classical.propDecidable
local instance selectedReferenceMetadataInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
    {outside : List ℕ} {l : ℕ} {p : Pattern (pairedHistoryType seed l)}
    (R S : BlockReference sources seed V outside l p)

@[simp] theorem left_historyFrequencies :
    historyFrequencies sources seed V l R.left.choices=R.leftFrequency :=
  historyFrequencies_assemble sources seed V l R.leftFrequency _

@[simp] theorem right_historyFrequencies :
    historyFrequencies sources seed V l R.right.choices=R.rightFrequency :=
  historyFrequencies_assemble sources seed V l R.rightFrequency _

theorem pairedDrawValues_eq :
    pairedDrawValues sources seed V l R.left.choices R.right.choices=expand p R.natDraw := by
  funext i
  cases i with
  | inl i =>
    exact congrArg (fun x : InternalSourceDraws sources seed l=>(x i).val)
      (historyDraws_assemble sources seed V l R.leftFrequency
        (fun j=>blockSourceDraws sources seed l p R.blockDraw R.valid (.inl j)))
  | inr i =>
    exact congrArg (fun x : InternalSourceDraws sources seed l=>(x i).val)
      (historyDraws_assemble sources seed V l R.rightFrequency
        (fun j=>blockSourceDraws sources seed l p R.blockDraw R.valid (.inr j)))

@[simp] theorem pairedDrawPattern_eq :
    pairedDrawPattern sources seed V l R.left.choices R.right.choices=p := by
  rw [pairedDrawPattern,R.pairedDrawValues_eq]
  exact patternOf_expand p R.natDraw

theorem sameLeftFrequencies (hroot : R.leftRoot.frequency=S.leftRoot.frequency)
    (hfreq : R.leftFrequency=S.leftFrequency) : R.left.SameFrequencies S.left := by
  refine ⟨hroot,?_⟩
  rw [R.left_historyFrequencies,S.left_historyFrequencies,hfreq]

theorem sameRightFrequencies (hroot : R.rightRoot.frequency=S.rightRoot.frequency)
    (hfreq : R.rightFrequency=S.rightFrequency) : R.right.SameFrequencies S.right := by
  refine ⟨hroot,?_⟩
  rw [R.right_historyFrequencies,S.right_historyFrequencies,hfreq]

theorem samePattern :
    pairedDrawPattern sources seed V l R.left.choices R.right.choices=
      pairedDrawPattern sources seed V l S.left.choices S.right.choices :=
  R.pairedDrawPattern_eq.trans S.pairedDrawPattern_eq.symm

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation.BlockReference

end

end OAI
