import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilyData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationRepresentativePatternsDecoded

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryCompensationRepresentativePatterns
attribute [local instance] Classical.propDecidable
local instance actualUniversalPrincipalPointRepresentativeInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ} {σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2)))}
  {J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
    SelectedBulkSample C l → ℤ → ℤ → ℂ}
  {α : Type} [Fintype α] {w : α→ℝ} {P Q : α→ℤ}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}

theorem matched_representative_eq_decoded
    (R : MatchedSelectedOuter C p o outside σ J w P Q i)
    (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
      |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)
    (hprime : ∀q∈outside,q.Prime) :
    R.representative hcell hprime=
      (decodedRepresentativeBlockEquiv C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) l p R.data.blockDraw R.data.valid
        R.witness.toReference.left R.witness.toReference.right i.2.1 i.2.2
        R.witness.toReference.left_matches R.witness.toReference.right_matches).symm := rfl

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
