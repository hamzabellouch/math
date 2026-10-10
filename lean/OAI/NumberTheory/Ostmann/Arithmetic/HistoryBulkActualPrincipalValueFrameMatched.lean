import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyMatchedMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrameScalars

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrameMatched
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryCompensationRepresentativePatterns
open HistoryBulkActualRootReferenceFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference HistoryGiantOriginalMeanFactorization HistorySignedXiTransport
open HistoryPairPattern HistoryGiantReferenceMean HistoryPairBulkTransport
open HistoryBulkFibreGiantApproximation HistoryBulkActualPrincipalBlockFamily
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkFibreSourceMean
open HistoryBulkPrincipalCollisionError HistoryBulkActualPrincipalValueFrame
attribute [local instance] Classical.propDecidable
local instance matchedValueFrameInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
  (hb : ∀i,(expand p b i).val∈(C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l i)).candidates)
  (outside : List ℕ) (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (a : SelectedNonbulkSample C l)
  (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
  (r : Witness C outside σ a (leftBlockDraws C p b hb) (rightBlockDraws C p b hb) J w P Q i)

theorem matchedWitnessPrincipalData_value_eq_frame
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l
      (leftChoices C (leftBlockDraws C p b hb) i)≠0)
    (he : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l
      (rightChoices C (rightBlockDraws C p b hb) i)≠0)
    (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
      |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)
    (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
    (corrected mixed : Bool) (u : SelectedBulkSample C l) :
    let f := witnessFrame C outside σ a
      (leftBlockDraws C p b hb) (rightBlockDraws C p b hb) J w P Q i r ha hc he hcell hp
    (matchedWitnessPrincipalData C p b hb outside σ a J w P Q i r ha hc he hcell
      (bulkSize k L/2) hlen hp hV true).value corrected mixed u =
      f.rootValue mixed hV σ (fibreAssignment C a u) *
        giantValue f corrected mixed (fibreAssignment C a u) := by
  dsimp only
  rw [giantValue_eq_giantScalar]
  simp only [MatchedPrincipalReferenceData.value, MatchedPrincipalReferenceData.amplitude,
    PrincipalAmplitudeData.value, matchedWitnessPrincipalData, Frame.rootValue,
    sourceBulkUnits_fibreAssignment]
  simp only [Frame.left, Frame.right, witnessFrame]
  rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrameMatched

end

end OAI
