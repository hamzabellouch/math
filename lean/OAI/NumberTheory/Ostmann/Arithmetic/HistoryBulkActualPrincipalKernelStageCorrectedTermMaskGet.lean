import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedTermMask
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageTermBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalKernelStage
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryBulkActualCorrectedPrincipalBlockFamily
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (outside : List ℕ) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands (Template.remainder (l+1)
    (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
  (hprime : ∀q∈outside,q.Prime)
  (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
  (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)

theorem selectedKernelMask_restore_get
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (u : SelectedBulkSample C l)
    (ho : (selectCorrectedOuterReference (l:=l) C p o outside e (v,f,g)).isSome) :
    selectedKernelMask (l:=l) C p outside e he hprime v f g
      (restoreOriginalDraw C l p o u) =
      CorrectedSelectedOuter.kernelStatic (C:=C) (l:=l) (p:=p) (o:=o)
        (outside:=outside) (e:=e) (i:=(v,f,g))
        ((selectCorrectedOuterReference (l:=l) C p o outside e (v,f,g)).get ho)
        he hprime u :=
  (selectedKernelMask_of_projections
    (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
    C p outside e he hprime v f g
    (restoreOriginalDraw C l p o u) o u
    (originalDrawOuter_restore C l p o u) (originalDrawBulk_restore C l p o u)).trans
    (option_match_get
      (α:=CorrectedSelectedOuter (l:=l) C p o outside e (v,f,g)) (β:=Prop)
      (selectCorrectedOuterReference (l:=l) C p o outside e (v,f,g)) False
      (fun R : CorrectedSelectedOuter (l:=l) C p o outside e (v,f,g) =>
        CorrectedSelectedOuter.kernelStatic (C:=C) (l:=l) (p:=p) (o:=o)
          (outside:=outside) (e:=e) (i:=(v,f,g)) R he hprime u) ho)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
