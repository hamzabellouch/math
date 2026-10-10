import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferencePattern
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationMatchedReference

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairRows HistoryCompensationRepresentativePatterns HistorySymbolicEncoding
open HistoryBulkFibreGiantApproximation HistoryPairReferenceFlagExpectation
open HistoryRepresentativeSourceSeparation HistoryBulkPrincipalBSquareReplacement
local instance squareReferenceMatchedInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz depth L E} {outside : List ℕ}
variable (r : Frame (l:=l) C outside)
variable {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize depth L/2)) depth) l)}
variable (B : MatchedBlockReference C.sources (Template.initial (2*(bulkSize depth L/2)) depth)
    (frequencyBound Bs BD Bz depth L) outside l p)
    (hl : leftDraw r=B.left) (hr : rightDraw r=B.right)

include hl hr

theorem slots_of_matchedBlockReference : ∀i,(slot r.left r.right (pairedInternalEquiv
    (Template.initial (2*(bulkSize depth L/2)) depth) r.left r.right
    (leftDraw r).labels (rightDraw r).labels i)).value=(expand p B.blockDraw i).val := by
  change ∀i,(slot (leftDraw r).history (rightDraw r).history
    (pairedOccurrenceEquiv (leftDraw r) (rightDraw r) i)).value=(expand p B.blockDraw i).val
  rw [hl,hr]
  intro i
  exact B.slot_values i

def principalSquareReference_of_matchedBlockReference
    (x : Frame.Source (C:=C) (l:=l)) (hx : (assignmentPrior C.sources _).mass x≠0)
    (had : PairAdmissible r.left r.right outside) (sw : ℕ) (hout : outside.length=2*sw)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz depth L j<q)
    (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l))) (K : ℕ) :
    PrincipalSquareReference C outside l p B.blockDraw.val :=
  principalSquareReference r x hx p B.blockDraw (slots_of_matchedBlockReference r B hl hr)
    had sw hout hV σ K

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference

end

end OAI
