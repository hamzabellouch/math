import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexCorrectedDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkFibreOriginalReference HistoryBulkIndependentFibreReference
open HistoryBulkFibreGiantApproximationReference HistoryPairRepresentatives
open HistoryPairReferenceSourceTransport HistoryBulkActualPrincipalBlockFamily
open HistoryBulkPrincipalBSquareReference HistoryBulkPrincipalBSquareReplacement
open HistoryBulkActualPrincipalSourceReindex HistoryRepresentativeSourceSeparation
open HistoryBulkReferencePeriodicMeanSource CanonicalHistoryLeafBulk
open HistoryDiagonalRemainingRootMatching
attribute [local instance] Classical.propDecidable
local instance correctedSquareInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ}{e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
namespace CorrectedSelectedOuter
variable (R : CorrectedSelectedOuter C p o outside e i)
  (he : PreservesRemainingBands _ e) (hprime : ∀q∈outside,q.Prime)

variable (had : PairAdmissible (R.frame he hprime).left (R.frame he hprime).right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j))
include hfreq

theorem rawBTerm_eq_squareBTerm (u : SelectedBulkSample C l)
    (hu : (selectedBulkPrior C l).mass u≠0) :
    R.rawBTerm he hprime u=R.squareBTerm he hprime had hout hV u := by
  have hleft := fibreAssignment_nonbulk_fixed C (outerNonbulk C l p o) u R.witness.bulk
  have hright : ∀j:Fin (SelectedTemplate k L l).length,
      ((SelectedTemplate k L l).get j).role≠.bulk →
      (R.squareRightSource he u j).val=((R.frame he hprime).rightSource j).val :=
    counterpartCurrentAssignment_nonbulk_fixed C
      (fibreAssignment C (outerNonbulk C l p o) R.witness.bulk)
      (fibreAssignment C (outerNonbulk C l p o) u) e he R.witness.compatible _ hleft
  have hbulk : ∀v : Frame.Slots (depth:=k) (L:=L) (l:=l),
      bulkSamples C.sources (2*(bulkSize k L/2)) k l (R.squareRightSource he u) v.1 v.2=
      bulkSamples C.sources (2*(bulkSize k L/2)) k l
        (fibreAssignment C (outerNonbulk C l p o) u) (R.permutation v).1 (R.permutation v).2 :=
    counterpartCurrentAssignment_remainingBulkSamples C
      (fibreAssignment C (outerNonbulk C l p o) u) e he _
  unfold rawBTerm squareBTerm
  rw [dite_eq_left hu]
  exact masked_mixed_eq_squareBFactor (l:=l) (R.frame he hprime)
    (fibreAssignment C (outerNonbulk C l p o) u) (R.squareSource_mass u hu)
    p R.data.blockDraw (slots_of_matchedBlockReference (l:=l)
      (R.frame he hprime) (R.blockReference he) rfl rfl)
    had hout hV R.permutation (R.squareRightSource he u) hfreq hbulk hleft hright true

theorem mean_rawBTerm_eq_squareBTerm :
    (selectedBulkPrior C l).cmean (R.rawBTerm he hprime)=
      (selectedBulkPrior C l).cmean (R.squareBTerm he hprime had hout hV) := by
  apply FinitePrior.cmean_congr_support
  exact R.rawBTerm_eq_squareBTerm he hprime had hout hV hfreq

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
