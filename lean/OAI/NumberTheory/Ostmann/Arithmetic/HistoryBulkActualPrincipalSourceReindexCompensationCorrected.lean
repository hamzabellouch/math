import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCompensationBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCorrectedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCompensation
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily HistoryBulkReferenceFrequencyFamily
open HistoryBulkFibreGiantErrorAverage HistoryBulkPrincipalSourceReindexWitness
open HistoryBulkPrincipalSourceReindex HistoryPairSourceLaws
open HistoryBulkFibreOriginalReference HistoryBulkFibreGiantApproximation
open HistoryBulkReferencePeriodicMeanSource HistoryGiantReferenceMean
open HistoryBulkIndependentFibreReference HistoryDiagonalRemainingRootMatching
local instance compensationCorrectedInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
  (hb : ∀j,(expand p b j).val∈(C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l j)).candidates)

theorem correctedWitnessPrincipal_div_blockJacobian
    (outside : List ℕ) (a : SelectedNonbulkSample C l)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e) (s t : ℤ)
    (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)
    (r : HistoryBulkActualCorrectedReferenceFamily.Witness C outside a e s t
      (leftChoices C (leftDraws C p b hb) i) (rightChoices C (rightDraws C p b hb) i))
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ _ l (leftChoices C (leftDraws C p b hb) i) ≠ 0)
    (hd : choicesMass C.sources _ _ l (rightChoices C (rightDraws C p b hb) i) ≠ 0)
    (hp : ∀q∈outside,q.Prime) :
    let f := HistoryBulkActualCorrectedReferenceFamily.witnessFrame C outside a e s t
      (leftChoices C (leftDraws C p b hb) i) (rightChoices C (rightDraws C p b hb) i)
      he ha hc hd hp r
    correctedWitnessPrincipal C outside a e he s t
      (leftChoices C (leftDraws C p b hb) i) (rightChoices C (rightDraws C p b hb) i)
      r ha hc hd hp / blockJacobian C p b =
      (selectedBulkPrior C l).cmean (fun u =>
        let y := rightAssignment C a e u (reference_compatible_all C outside a e he s t
          (leftChoices C (leftDraws C p b hb) i) (rightChoices C (rightDraws C p b hb) i) r u)
        staticPairMask (f.newLeft (fibreAssignment C a u)) (f.newRight y) outside *
          f.principalCorrectedMixed (bulkPermutation e he) (fibreAssignment C a u) y) := by
  dsimp only
  dsimp only [correctedWitnessPrincipal]
  rw [frame_oldCompensation]
  change ((pairedChoiceCompensation C (leftChoices C (leftDraws C p b hb) i)
    (rightChoices C (rightDraws C p b hb) i):ℂ)*_) / blockJacobian C p b = _
  rw [pairedChoiceCompensation_eq_blockJacobian]
  rw [mul_comm,mul_div_cancel_right₀ _ (blockJacobian_ne_zero C p b)]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCompensation

end

end OAI
