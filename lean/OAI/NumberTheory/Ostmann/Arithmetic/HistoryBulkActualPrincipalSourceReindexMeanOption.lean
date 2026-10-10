import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMatched
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMeanOptionBasic

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
open HistoryBulkActualPrincipalSourceReindexFamily
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
  (J : Background C l → Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
    SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
  (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
  (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
    |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hp : ∀q∈outside,q.Prime)
  (hAd : ∀r : Frame (l:=l) C outside, PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

open HistoryBulkActualPrincipalSourceReindex HistoryBulkUniversalPatternAggregation

variable (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j))
include hfreq

theorem plain_prime_raw_option_cmean_eq_square (bg : Background C l)
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    (selectedOuter (l:=l) C outside σ (J bg) w P Q hactual hl houtside hw hpos bg i p b).elim 0
      (fun R=>(selectedBulkPrior C l).cmean (R.rawBTerm (l:=l) hcell hp false false))=
    (selectedBulkPrior C l).cmean
      (fun u=>(selectedOuter (l:=l) C outside σ (J bg) w P Q hactual hl houtside hw hpos bg i p b).elim 0
        (fun R=>R.squareBTerm (l:=l) hcell hp (hAd (R.frame (l:=l) hcell hp)) hout hV false false u)) := by
  exact option_cmean_congr (selectedBulkPrior C l)
    (selectedOuter (l:=l) C outside σ (J bg) w P Q hactual hl houtside hw hpos bg i p b)
    (fun R=>R.rawBTerm (l:=l) hcell hp false false)
    (fun R=>R.squareBTerm (l:=l) hcell hp (hAd (R.frame (l:=l) hcell hp)) hout hV false false)
    (fun R=>R.mean_rawBTerm_prime_eq_squareBTerm (l:=l) hcell hp
      (hAd (R.frame (l:=l) hcell hp)) hout hV hfreq)

theorem plain_mixed_raw_option_cmean_eq_square (corrected : Bool) (bg : Background C l)
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    (selectedOuter (l:=l) C outside σ (J bg) w P Q hactual hl houtside hw hpos bg i p b).elim 0
      (fun R=>(selectedBulkPrior C l).cmean (R.rawBTerm (l:=l) hcell hp corrected true))=
    (selectedBulkPrior C l).cmean
      (fun u=>(selectedOuter (l:=l) C outside σ (J bg) w P Q hactual hl houtside hw hpos bg i p b).elim 0
        (fun R=>R.squareBTerm (l:=l) hcell hp (hAd (R.frame (l:=l) hcell hp)) hout hV corrected true u)) := by
  exact option_cmean_congr (selectedBulkPrior C l)
    (selectedOuter (l:=l) C outside σ (J bg) w P Q hactual hl houtside hw hpos bg i p b)
    (fun R=>R.rawBTerm (l:=l) hcell hp corrected true)
    (fun R=>R.squareBTerm (l:=l) hcell hp (hAd (R.frame (l:=l) hcell hp)) hout hV corrected true)
    (fun R=>R.mean_rawBTerm_mixed_eq_squareBTerm (l:=l) hcell hp
      (hAd (R.frame (l:=l) hcell hp)) hout hV hfreq corrected)

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI
