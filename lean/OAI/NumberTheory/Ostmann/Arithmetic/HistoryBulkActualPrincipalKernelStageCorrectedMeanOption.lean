import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedMeanAlgebra
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedMeanMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedNormalize
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedOptionDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedRestored

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryBulkActualCorrectedPrincipalBlockFamily HistoryBulkPrincipalKernelReplacementMatched
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (outside : List ℕ) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands (Template.remainder (l+1)
    (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
  (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)

theorem restoredOption_eq_jacobian_option
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (symbolic : Bool) (u : SelectedBulkSample C l)
    (ho : outerMass C l p o≠0) (hu : (selectedBulkPrior C l).mass u≠0) :
    (selectCorrectedOuterReference (l:=l) C p o outside e (v,f,g)).elim 0
      (fun R : CorrectedSelectedOuter (l:=l) C p o outside e (v,f,g) =>
        CorrectedSelectedOuter.restoredKernelTerm (C:=C) (l:=l) (p:=p) (o:=o)
          (outside:=outside) (e:=e) (i:=(v,f,g)) R he hlen hprime hV symbolic u) =
    (∏q : Block p,((outerBlocks C l p o q).val:ℂ))*
      selectedKernelOptionValue (l:=l) C p outside e he hlen hprime hV v f g o symbolic u :=
  option_elim_mul_of_eq
    (selectCorrectedOuterReference (l:=l) C p o outside e (v,f,g))
    (∏q : Block p,((outerBlocks C l p o q).val:ℂ))
    (fun R : CorrectedSelectedOuter (l:=l) C p o outside e (v,f,g) =>
      CorrectedSelectedOuter.restoredKernelTerm (C:=C) (l:=l) (p:=p) (o:=o)
        (outside:=outside) (e:=e) (i:=(v,f,g)) R he hlen hprime hV symbolic u)
    (fun R : CorrectedSelectedOuter (l:=l) C p o outside e (v,f,g) =>
      CorrectedSelectedOuter.kernelTerm (C:=C) (l:=l) (p:=p) (o:=o)
        (outside:=outside) (e:=e) (i:=(v,f,g)) R he hlen hprime hV symbolic u)
    (fun R : CorrectedSelectedOuter (l:=l) C p o outside e (v,f,g) =>
      CorrectedSelectedOuter.restoredKernelTerm_eq_jacobian_mul (C:=C) (l:=l) (p:=p) (o:=o)
        (outside:=outside) (e:=e) (i:=(v,f,g)) R he hlen hprime hV symbolic u
        (originalDrawMass_restore_ne_zero C l p o u ho hu))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
