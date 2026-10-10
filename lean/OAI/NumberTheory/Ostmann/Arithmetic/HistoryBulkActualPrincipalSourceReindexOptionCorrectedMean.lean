import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCorrectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionCorrectedSource

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily HistoryBulkReferenceFrequencyFamily
open HistoryBulkFibreGiantErrorAverage HistoryBulkPrincipalSourceReindexWitness
open HistoryBulkActualPrincipalBlockFamily HistoryPairReferenceFlagExpectation
open HistoryBulkActualPrincipalSourceReindexPattern HistoryBulkActualPrincipalSourceReindexCompensation
open HistoryBulkActualGoodPrincipal HistoryBulkIndependentFibreReference
open HistoryBulkFibreOriginalReference
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
  (spectator : PrimeSource)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e)
  (ds : Fin (2*(bulkSize k L/2))→spectator.Sample)
  (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)

private theorem rawBTerm_eq_bulkPermutation
    (R : CorrectedSelectedOuter C p o (spectatorList spectator ds) e i)
    (u : SelectedBulkSample C l) :
    R.rawBTerm he (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) u =
      let f := R.frame he (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
      let x := fibreAssignment C (outerNonbulk C l p o) u
      let y := R.squareRightSource he u
      HistoryBulkReferencePeriodicMeanSource.staticPairMask
        (f.newLeft x) (f.newRight y) (spectatorList spectator ds)*
        f.principalCorrectedMixed (bulkPermutation e he) x y :=
  congrArg (fun σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2)))=>
    let f := R.frame he (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)
    let x := fibreAssignment C (outerNonbulk C l p o) u
    let y := R.squareRightSource he u
    HistoryBulkReferencePeriodicMeanSource.staticPairMask
      (f.newLeft x) (f.newRight y) (spectatorList spectator ds)*
      f.principalCorrectedMixed σ x y)
    (R.permutation_eq_bulkPermutation he)

theorem corrected_constructor_div
    (D : OuterData C p o)
    (r : HistoryBulkActualCorrectedReferenceFamily.Witness C (spectatorList spectator ds)
      (outerNonbulk C l p o) e i.1.val i.1.val
      (leftChoices C (leftBlockDraws C p D.blockDraw D.valid) i)
      (rightChoices C (rightBlockDraws C p D.blockDraw D.valid) i)) :
    correctedWitnessPrincipal C (spectatorList spectator ds) (outerNonbulk C l p o) e he
      i.1.val i.1.val (leftChoices C (leftBlockDraws C p D.blockDraw D.valid) i)
      (rightChoices C (rightBlockDraws C p D.blockDraw D.valid) i) r D.nonbulk_pos
      (D.left_mass i) (D.right_mass i)
      (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds) /
        blockJacobian C p D.blockDraw =
      (selectedBulkPrior C l).cmean
        ((⟨D,r⟩ : CorrectedSelectedOuter C p o (spectatorList spectator ds) e i).rawBTerm he
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)) :=
  (correctedWitnessPrincipal_div_blockJacobian (l:=l) C p D.blockDraw D.valid
    (spectatorList spectator ds) (outerNonbulk C l p o) e he i.1.val i.1.val i r
    D.nonbulk_pos (D.left_mass i) (D.right_mass i)
    (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)).trans
    (congrArg ((selectedBulkPrior C l).cmean)
      (funext fun u=>rawBTerm_eq_bulkPermutation C p o spectator e he ds i ⟨D,r⟩ u)).symm

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
