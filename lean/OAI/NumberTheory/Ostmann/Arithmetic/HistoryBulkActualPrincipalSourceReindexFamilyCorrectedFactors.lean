import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrectedFalse

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrected
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalBSquareReplacement HistoryRepresentativeSourceSeparation
open HistoryBulkReferencePeriodicMeanSource HistoryBulkActualGoodPrincipal
open HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands _ e) (hp : ∀q∈outside,q.Prime)
  (hAd : ∀r : Frame (l:=l) C outside, PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (bg : Background C l) (u : SelectedBulkSample C l)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

variable (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : Block p → CommonSample C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))

theorem densityPatternFactor_eq (probability : Bool) :
    densityPatternFactor
      (referenceFamily C outside e he hp hAd hout hV bg u i)
      (densitySources C outside e he hp bg u i) probability true true
      (staticMask C outside e he hp bg u i) p b =
    selectedTerm C outside e he hp hAd hout hV bg u i p b probability := by
  by_cases hu : (selectedBulkPrior C l).mass u≠0
  · cases hr : selectedOuter C outside e bg i p b with
    | none =>
      have hf : referenceFamily C outside e he hp hAd hout hV bg u i p b=none := by
        unfold referenceFamily
        rw [dite_eq_left hu,hr]
        rfl
      rw [HistoryBulkActualPrincipalSourceReindexFamilyBasic.factor_of_none _ _ _ _ _ _ _ _ hf]
      unfold selectedTerm
      rw [hr]
      rfl
    | some R =>
      let S : PrincipalSquareReference C outside l p b :=
        R.squareReference (l:=l) he hp (hAd (R.frame (l:=l) he hp)) hout hV u hu
      have hf : referenceFamily C outside e he hp hAd hout hV bg u i p b=some S := by
        unfold referenceFamily
        rw [dite_eq_left hu,hr]
        rfl
      rw [HistoryBulkActualPrincipalSourceReindexFamilyBasic.factor_of_some _ _ _ _ _ _ _ _ S hf]
      have hx : densitySources C outside e he hp bg u i p b=(R.frame (l:=l) he hp).leftSource := by
        unfold densitySources
        rw [hr]
        rfl
      rw [hx]
      have hm : staticMask C outside e he hp bg u i p b =
          staticCondition C outside e he hp bg u i p b R := by
        apply propext
        unfold staticMask
        rw [hr]
        exact and_iff_right hu
      rw [hm]
      have ht : selectedTerm C outside e he hp hAd hout hV bg u i p b probability =
          (if staticCondition C outside e he hp bg u i p b R then 1 else 0) *
            (Frame.extractedDensity (C:=C) (R.frame (l:=l) he hp).leftSource *
              (S.principal.value true true S.newBulk *
                (if probability then probabilityProduct S true else bMean S true))) := by
        unfold selectedTerm
        rw [hr]
        change squareTerm C outside e he hp hAd hout hV bg u i p b R probability = _
        unfold squareTerm
        rw [dite_eq_left hu]
        rfl
      rw [ht]
      exact mul_left_comm _ _ _
  · have hf : referenceFamily C outside e he hp hAd hout hV bg u i p b=none := by
      unfold referenceFamily
      rw [dite_eq_right hu]
    rw [HistoryBulkActualPrincipalSourceReindexFamilyBasic.factor_of_none _ _ _ _ _ _ _ _ hf]
    unfold selectedTerm
    cases selectedOuter C outside e bg i p b with
    | none => rfl
    | some R =>
      change 0 = squareTerm C outside e he hp hAd hout hV bg u i p b R probability
      unfold squareTerm
      rw [dite_eq_right hu]

theorem densityPatternFactor_false_eq :
    densityPatternFactor
      (referenceFamily C outside e he hp hAd hout hV bg u i)
      (densitySources C outside e he hp bg u i) false true true
      (staticMask C outside e he hp bg u i) p b =
    (selectedOuter C outside e bg i p b).elim 0
      (fun R=>R.squareBTerm (l:=l) he hp (hAd (R.frame (l:=l) he hp)) hout hV u) := by
  rw [densityPatternFactor_eq]
  unfold selectedTerm
  cases selectedOuter C outside e bg i p b with
  | none => rfl
  | some R => exact squareTerm_false C outside e he hp hAd hout hV bg u i p b R

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrected

end

end OAI
