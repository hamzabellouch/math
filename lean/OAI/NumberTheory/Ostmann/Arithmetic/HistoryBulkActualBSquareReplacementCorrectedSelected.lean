import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementBoundInterface
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementCorrectedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementGeometryInterface
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementZeroCost

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkActualRootReferenceFamily HistoryBulkActualPrincipalBlockFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkPrincipalBSquareReplacement HistoryRepresentativeSourceSeparation
open HistoryBulkActualPrincipalSourceReindexFamilyCorrected HistoryBulkIndependentFibreReference Filter
attribute [local instance] Classical.propDecidable
local instance actualBSquareCorrectedSelectedInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_corrected_errors_eventually (d : Decomposition)
    (Bs BD Bz H : ℝ) {k : ℕ} (hBs : 0≤Bs) (hH : 0≤H) (hk : 2≤k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀q:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (q:ℕ) ∧
        Real.log (q:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀(outside : List ℕ)(_houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
        (hout : outside.length=2*(bulkSize k L/2)),
      ∀l,l<k →
      ∃(hp : ∀q∈outside,q.Prime)
        (hAd : ∀r : Frame (l:=l) C outside,PairAdmissible r.left r.right outside)
        (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q),
      ∀(e : RemainingPermutation (k:=k) (L:=L) (l:=l))(he : PreservesRemainingBands _ e),
      (correctedFrequencyError C outside e he hp hAd hout hV ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
        correctedFrequencyError C outside e he hp hAd hout hV ≤
          Real.exp (-H*(bulkSize k L:ℝ))) ∧
      (‖correctedSourceMean C outside e he hp hAd hout hV false-
          correctedSourceMean C outside e he hp hAd hout hV true‖ ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
        ‖correctedSourceMean C outside e he hp hAd hout hV false-
          correctedSourceMean C outside e he hp hAd hout hV true‖ ≤
          Real.exp (-H*(bulkSize k L:ℝ))) :=
  ((selected_square_inputs_eventually d Bs BD Bz (lt_of_lt_of_le (Nat.zero_lt_succ 1) hk)).and
    (selected_root_density_B_replacement_interface d Bs BD Bz 0 H hBs hH hk)).mono
    (fun L h E C hG hGu hcl hcu hb hd spectator hspec outside houtside hout l hl =>
      let hp : ∀q∈outside,q.Prime := fun q hq =>
        Exists.elim (houtside q hq) (fun r hr => hr ▸ spectator.prime r.val r.property)
      let hmem : ∀q∈outside,q∈spectator.candidates := fun q hq =>
        Exists.elim (houtside q hq) (fun r hr => hr ▸ r.property)
      let hg := h.1 E C hG hcl hcu hb hd spectator hspec outside hmem l hl.le
      let hV := hg.1
      let hAd := hg.2
      let hsize : outside.length≤bulkSize k L := hout.symm ▸ Nat.mul_div_le (bulkSize k L) 2
      let hlog : ∀q∈outside,Real.log (q:ℝ)≤Real.exp ((1/1000:ℝ)*L) := fun q hq =>
        Exists.elim (houtside q hq) (fun r hr => hr ▸ (hspec r).2)
      ⟨hp,hAd,hV,fun e he =>
        let hbnd := h.2 E C hG hGu hcl hcu hb hd spectator hspec l true true hl
          outside (fun q hq => (hp q hq).pos) hsize hlog
          (Background C l × SelectedBulkSample C l)
          (FinitePrior.pair (backgroundPrior C l) (selectedBulkPrior C l))
          (fun v f g a => referenceFamily C outside e he hp hAd hout hV a.1 a.2 (v,(f,g)))
          (fun v f g a => densitySources C outside e he hp a.1 a.2 (v,(f,g)))
          (fun v f g a => staticMask C outside e he hp a.1 a.2 (v,(f,g)))
        let hfreq := zero_cost_bounds L (correctedFrequencyError C outside e he hp hAd hout hV)
          (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
          (Real.exp (-H*(bulkSize k L:ℝ))) hbnd
        let hn := norm_correctedSourceMean_sub_le_correctedFrequencyError C outside e he hp hAd hout hV
        ⟨hfreq,hn.trans hfreq.1,hn.trans hfreq.2⟩⟩)

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI
