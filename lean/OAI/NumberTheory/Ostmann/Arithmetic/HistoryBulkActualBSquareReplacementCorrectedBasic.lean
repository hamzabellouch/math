import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrectedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalBSquareReplacement HistoryRepresentativeSourceSeparation
open HistoryBulkReferenceFrequencyFamily
open HistoryBulkActualPrincipalSourceReindexFamilyCorrected
open HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable
local instance actualBSquareCorrectedBasicInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e) (hp : ∀q∈outside,q.Prime)
  (hAd : ∀r : Frame (l:=l) C outside, PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

def correctedSourceMean (probability : Bool) : ℂ :=
  (backgroundPrior C l).cmean (fun bg => (selectedBulkPrior C l).cmean (fun u =>
    rootExpression C outside e he hp hAd hout hV
      bg u probability))

def correctedFrequencyError : ℝ :=
  ∑v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
    ∑f : FrequencyChoices (frequencyBound Bs BD Bz k L) l,
      ∑g : FrequencyChoices (frequencyBound Bs BD Bz k L) l,
        ‖(FinitePrior.pair (backgroundPrior C l) (selectedBulkPrior C l)).cmean
            (fun a => expression C outside e he hp hAd hout hV a.1 a.2 (v,(f,g)) false) -
          (FinitePrior.pair (backgroundPrior C l) (selectedBulkPrior C l)).cmean
            (fun a => expression C outside e he hp hAd hout hV a.1 a.2 (v,(f,g)) true)‖

theorem norm_correctedSourceMean_sub_le_correctedFrequencyError  :
    ‖correctedSourceMean C outside e he hp hAd hout hV
        false -
      correctedSourceMean C outside e he hp hAd hout hV
        true‖ ≤
      correctedFrequencyError C outside e he hp hAd hout hV
 :=
  norm_nested_root_sum_sub_le (backgroundPrior C l) (selectedBulkPrior C l)
    (fun bg u i => expression C outside e he hp hAd hout hV bg u i false)
    (fun bg u i => expression C outside e he hp hAd hout hV bg u i true)

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI
