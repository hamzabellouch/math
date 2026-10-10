import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTermSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedDensityRoot
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSelectedInputs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkActualPrincipalBlockFamily HistoryBulkPrincipalKernelReplacementMatched Filter
attribute [local instance] Classical.propDecidable
local instance selectedKernelSumInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_kernel_sum_errors_eventually (d : Decomposition)
    (Bs BD Bz H : ℝ) {k : ℕ} (hBs : 0≤Bs) (hH : 0≤H) (hk : 0<k) :
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
      ∃hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator,
      ∀(outside : List ℕ)(houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
        (hlen : outside.length=2*(bulkSize k L/2)),
      ∀l (hl : l≤k),
      ∃(hprime : ∀q∈outside,q.Prime)
        (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q),
      ∀(σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
        (J : (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
          OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p →
          Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
          SelectedBulkSample C l → ℤ → ℤ → ℂ)
        (α : Type) [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
        (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
        (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
          |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧
          |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
        (corrected mixed : Bool), (if corrected then l<k else l≤k) →
      let S := fun symbolic => ∑v,∑f,∑g,∑p,
        selectedKernelMean C p outside σ (J p) w P Q hactual hl houtside hw hpos hcell
          hlen hprime hV v f g symbolic corrected mixed
      ‖S false-S true‖≤Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖S false-S true‖≤Real.exp (-H*(bulkSize k L:ℝ)) :=
  (((HistoryBulkFixedReferenceTerm.selected_reference_equality_eventually d Bs BD Bz hk).and
    (HistoryBulkSupportConverse.selected_source_inputs_eventually d Bs BD Bz hk)).and
    (selected_root_density_principal_kernel_error_eventually d Bs BD Bz 0 H hBs hH hk)).mono
    (fun L h E C hG hGu hcl hcu hb hd spectator hspec =>
      let hactual := h.1.1 E C hG hcl hcu hb hd spectator hspec
      let hsf := (h.1.2 E C hG hcl hcu hb hd spectator hspec).2.2
      ⟨hactual,fun outside houtside hlen l hl =>
        let hprime : ∀q∈outside,q.Prime := fun q hq =>
          (houtside q hq).elim (fun r hr => hr ▸ spectator.prime r.val r.property)
        let hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q := fun q hq j hj =>
          (houtside q hq).elim (fun r hr => hr ▸ hsf r j (hj.trans hl))
        ⟨hprime,hV,fun σ J _α _ w P Q hw hpos hcell corrected mixed hdepth =>
          let F := fun v f g p => matchedPrincipalFamily C p outside σ (J p) w P Q
            hactual hl houtside hw hpos hcell (bulkSize k L/2) hlen hprime hV true v f g
          let X := fun v f g p => selectedKernelDensitySources C p outside σ (J p) w P Q
            hactual hl houtside hw hpos hcell hlen hprime hV v f g
          let mask := fun v f g p => selectedKernelMask C p outside σ (J p) w P Q
            hactual hl houtside hw hpos hcell hprime v f g
          four_sum_zero_cost_bounds
            (fun v f g p => densityPrincipalProductMean false (F v f g p) (X v f g p) corrected mixed (mask v f g p))
            (fun v f g p => densityPrincipalProductMean true (F v f g p) (X v f g p) corrected mixed (mask v f g p))
            (fun v f g p => densityPrincipalDifferenceMean (F v f g p) (X v f g p) corrected mixed (mask v f g p))
            (fun v f g p => densityPrincipalProductMean_sub (F v f g p) (X v f g p) corrected mixed (mask v f g p))
            L (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
              (Real.exp (-H*(bulkSize k L:ℝ)))
            (h.2 E C hG hGu hcl hcu hb hd spectator hspec l corrected mixed hdepth outside
              (fun q hq => (hprime q hq).pos)
              (hlen.symm ▸ Nat.mul_div_le (bulkSize k L) 2)
              (fun q hq => (houtside q hq).elim (fun r hr => hr ▸ (hspec r).2))
              F (fun v f g p o ho => matchedPrincipalFamily_reference_giants C p outside σ (J p) w P Q
                hactual hl houtside hw hpos hcell (bulkSize k L/2) hlen hprime hV true v f g o ho)
              X mask)⟩⟩)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end

end OAI
