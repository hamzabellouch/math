import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMeanDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexMeanPoint

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
attribute [local instance] HistoryBulkPrincipalBSquareReplacement.squareDensityBasicInternalDecidable
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

open HistoryBulkUniversalPatternAggregation

variable (corrected mixed : Bool) (bg : Background C l)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

def rawBackgroundPoint
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) : ℂ :=
  (selectedOuter (l:=l) C outside σ (J bg) w P Q hactual hl houtside hw hpos bg i p b).elim 0
    (fun R=>(selectedBulkPrior C l).cmean (R.rawBTerm (l:=l) hcell hp corrected mixed))

def densityBackgroundPoint (u : SelectedBulkSample C l)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) : ℂ :=
  densityPatternFactor (C:=C) (l:=l)
    (referenceFamily (l:=l) C outside σ (J bg) w P Q hactual hl houtside hw hpos hcell hp hAd hout hV bg u i)
    (densitySources (l:=l) C outside σ (J bg) w P Q hactual hl houtside hw hpos hcell hp bg u i)
    false corrected mixed
    (staticMask (l:=l) C outside σ (J bg) w P Q hactual hl houtside hw hpos hcell hp bg u i) p b

variable (hfreq : ∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j))
include hfreq

theorem rawBackgroundPoint_eq_density (hmode : corrected=false ∨ mixed=true)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) :
    rawBackgroundPoint C outside σ J w P Q hactual hl houtside hw hpos hcell hp corrected mixed bg i p b =
      (selectedBulkPrior C l).cmean (fun u=>
        densityBackgroundPoint C outside σ J w P Q hactual hl houtside hw hpos hcell hp hAd hout hV corrected mixed bg i u p b) :=
  raw_point_eq_density_cmean (l:=l) C outside σ J w P Q hactual hl houtside hw hpos
    hcell hp hAd hout hV hfreq corrected mixed hmode bg p b i

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI
