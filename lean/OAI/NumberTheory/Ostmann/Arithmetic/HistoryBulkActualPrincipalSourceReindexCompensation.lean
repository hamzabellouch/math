import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCompensationBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAveragePrincipal

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
local instance compensationPrincipalInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
  (hb : ∀j,(expand p b j).val∈(C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l j)).candidates)

theorem primeWitnessPrincipal_div_blockJacobian
    (outside : List ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (a : SelectedNonbulkSample C l)
    (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)
    (r : Witness C outside σ a (leftDraws C p b hb) (rightDraws C p b hb)
      (fun _ _ _ _ => 1) (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ _ l (leftChoices C (leftDraws C p b hb) i) ≠ 0)
    (he : choicesMass C.sources _ _ l (rightChoices C (rightDraws C p b hb) i) ≠ 0)
    (hp : ∀q∈outside,q.Prime) :
    let f := primeWitnessFrame C outside σ a (leftDraws C p b hb) (rightDraws C p b hb)
      (fun _ _ _ _ => 1) r ha hc he hp
    primeWitnessPrincipal C outside σ a (leftDraws C p b hb) (rightDraws C p b hb)
      r ha hc he hp / blockJacobian C p b =
      (selectedBulkPrior C l).cmean (fun u =>
        staticPairMask (f.newLeft (fibreAssignment C a u))
          (f.newRight (permuteAssignment C σ (fibreAssignment C a u))) outside *
          f.principal σ (fibreAssignment C a u) (permuteAssignment C σ (fibreAssignment C a u))) := by
  dsimp only
  dsimp only [primeWitnessPrincipal]
  rw [frame_oldCompensation]
  change ((pairedChoiceCompensation C (leftChoices C (leftDraws C p b hb) i)
    (rightChoices C (rightDraws C p b hb) i):ℂ)*_) / blockJacobian C p b = _
  rw [pairedChoiceCompensation_eq_blockJacobian]
  rw [mul_comm,mul_div_cancel_right₀ _ (blockJacobian_ne_zero C p b)]

theorem mixedWitnessPrincipal_div_blockJacobian
    (outside : List ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (a : SelectedNonbulkSample C l)
    (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)
    (r : Witness C outside σ a (leftDraws C p b hb) (rightDraws C p b hb)
      (fun i => plainMixedWeight C outside a i.1.val) (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ _ l (leftChoices C (leftDraws C p b hb) i) ≠ 0)
    (he : choicesMass C.sources _ _ l (rightChoices C (rightDraws C p b hb) i) ≠ 0)
    (hp : ∀q∈outside,q.Prime) :
    let f := mixedWitnessFrame C outside σ a (leftDraws C p b hb) (rightDraws C p b hb)
      (fun i => plainMixedWeight C outside a i.1.val) r ha hc he hp
    mixedWitnessPrincipal C outside σ a (leftDraws C p b hb) (rightDraws C p b hb)
      r ha hc he hp / blockJacobian C p b =
      (selectedBulkPrior C l).cmean (fun u =>
        staticPairMask (f.newLeft (fibreAssignment C a u))
          (f.newRight (permuteAssignment C σ (fibreAssignment C a u))) outside *
          f.principalMixed σ (fibreAssignment C a u) (permuteAssignment C σ (fibreAssignment C a u))) := by
  dsimp only
  dsimp only [mixedWitnessPrincipal]
  rw [frame_oldCompensation]
  change ((pairedChoiceCompensation C (leftChoices C (leftDraws C p b hb) i)
    (rightChoices C (rightDraws C p b hb) i):ℂ)*_) / blockJacobian C p b = _
  rw [pairedChoiceCompensation_eq_blockJacobian]
  rw [mul_comm,mul_div_cancel_right₀ _ (blockJacobian_ne_zero C p b)]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCompensation

end

end OAI
