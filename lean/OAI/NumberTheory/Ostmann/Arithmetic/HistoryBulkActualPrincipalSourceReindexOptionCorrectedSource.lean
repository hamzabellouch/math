import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCorrectedSelectedDefs

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
open HistoryBulkIndependentFibreReference
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

private theorem correctedSelectedPrincipal_eq_option
    (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
    (ha : 0<(selectedNonbulkPrior C l).mass a)
    (hx : (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass x≠0)
    (hy : (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass y≠0) :
    correctedSelectedPrincipal (l:=l) C spectator e he ds a x y i=
      (HistoryBulkActualCorrectedReferenceFamily.selectWitness C (spectatorList spectator ds)
        a e i.1.val i.1.val (leftChoices C x i) (rightChoices C y i) ha).elim 0
        (fun r=>correctedWitnessPrincipal C (spectatorList spectator ds) a e he
          i.1.val i.1.val (leftChoices C x i) (rightChoices C y i) r ha
          (leftChoices_mass_of_draws C x hx i) (rightChoices_mass_of_draws C y hy i)
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)) :=
  (dite_eq_left ha).trans ((dite_eq_left hx).trans (dite_eq_left hy))

private theorem correctedPattern_eq_option
    (a : SelectedNonbulkSample C l)
    (b : BlockDraw p (CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
    (hb : ∀j,(expand p b j).val∈
      (C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l j)).candidates)
    (ha : 0<(selectedNonbulkPrior C l).mass a)
    (hx : (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass
      (leftBlockDraws C p b hb)≠0)
    (hy : (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l).mass
      (rightBlockDraws C p b hb)≠0) :
    drawPatternValue C spectator (correctedSelectedPrincipal (l:=l) C spectator e he)
      ds a i p b.val=
      (HistoryBulkActualCorrectedReferenceFamily.selectWitness C (spectatorList spectator ds)
        a e i.1.val i.1.val (leftChoices C (leftBlockDraws C p b hb) i)
        (rightChoices C (rightBlockDraws C p b hb) i) ha).elim 0
        (fun r=>correctedWitnessPrincipal C (spectatorList spectator ds) a e he
          i.1.val i.1.val (leftChoices C (leftBlockDraws C p b hb) i)
          (rightChoices C (rightBlockDraws C p b hb) i) r ha
          (leftChoices_mass_of_draws C _ hx i) (rightChoices_mass_of_draws C _ hy i)
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)) /
        blockJacobian C p b :=
  (drawPatternValue_of_valid (l:=l) C spectator
    (correctedSelectedPrincipal (l:=l) C spectator e he) ds a i p b hb).trans
    (congrArg (fun z : ℂ=>z/blockJacobian C p b)
      (correctedSelectedPrincipal_eq_option C spectator e he ds i a
        (leftBlockDraws C p b hb) (rightBlockDraws C p b hb) ha hx hy))

theorem correctedOuterPattern_eq_option (D : OuterData C p o) :
    drawPatternValue C spectator (correctedSelectedPrincipal (l:=l) C spectator e he)
      ds (outerNonbulk C l p o) i p (outerBlocks C l p o)=
      (HistoryBulkActualCorrectedReferenceFamily.selectWitness C (spectatorList spectator ds)
        (outerNonbulk C l p o) e i.1.val i.1.val
        (leftChoices C (leftBlockDraws C p D.blockDraw D.valid) i)
        (rightChoices C (rightBlockDraws C p D.blockDraw D.valid) i) D.nonbulk_pos).elim 0
        (fun r=>correctedWitnessPrincipal C (spectatorList spectator ds) (outerNonbulk C l p o)
          e he i.1.val i.1.val (leftChoices C (leftBlockDraws C p D.blockDraw D.valid) i)
          (rightChoices C (rightBlockDraws C p D.blockDraw D.valid) i) r D.nonbulk_pos
          (D.left_mass i) (D.right_mass i)
          (HistoryBulkGiantPrincipalTransport.selected_spectator_primes spectator ds)) /
        blockJacobian C p D.blockDraw :=
  @correctedPattern_eq_option d Bs BD Bz L k l E C p spectator e he ds i
    (outerNonbulk C l p o) D.blockDraw D.valid D.nonbulk_pos
    (@outerData_left_mass d Bs BD Bz L k l E C p o D i)
    (@outerData_right_mass d Bs BD Bz L k l E C p o D i)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
