import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrameMatched

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalCollisionError HistoryBulkFibreIntegralReplacementFrame
open HistoryBulkActualPrincipalValueFrameMatched
attribute [local instance] Classical.propDecidable
local instance actualCollisionValueInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ}
  {σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))}
  {J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ}
  {α : Type} [Fintype α] {w : α→ℝ} {P Q : α→ℤ}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
namespace MatchedSelectedOuter
variable (R : MatchedSelectedOuter C p o outside σ J w P Q i)
  (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
    |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem collisionReference_value_eq_frame (corrected mixed : Bool) (u : SelectedBulkSample C l) :
    (R.collisionReference hcell hlen hp hV).value corrected mixed u =
      (R.frame hcell hp).rootValue mixed hV σ (fibreAssignment C (outerNonbulk C l p o) u) *
        giantValue (R.frame hcell hp) corrected mixed (fibreAssignment C (outerNonbulk C l p o) u) := by
  rw [collisionReference_value]
  exact matchedWitnessPrincipalData_value_eq_frame C p R.data.blockDraw R.data.valid outside σ
    (outerNonbulk C l p o) J w P Q i R.witness R.data.nonbulk_pos (R.data.left_mass i)
    (R.data.right_mass i) hcell hlen hp hV corrected mixed u

end MatchedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
