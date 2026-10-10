import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTermSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion Filter CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryBulkSourceDisintegration HistoryBulkUniversalPatternAggregation
open HistoryBulkActualPrincipalBlockFamily
attribute [local instance] Classical.propDecidable
local instance universalPrincipalActualInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_aggregate_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) (hBs : 0≤Bs) (hBD : 0≤BD) (hBz : 0≤Bz)
    {k : ℕ} (hk : 2≤k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
    ∀spectator : PrimeSource,
      (∀p:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∃hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator,
    ∀(outside : List ℕ)(hout : ∀q∈outside,q∈spectator.candidates),
      outside.length=2*(bulkSize k L/2) → ∀(l : ℕ)(hl : l≤k),
    ∃hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q,
    ∀mixed : Bool,
      ‖selectedAggregate C outside hactual hl hout mixed hV‖ ≤
        Real.exp ((2:ℝ)^l*(initialGap Bs k L+16*(bulkSize k L:ℝ))) := by
  filter_upwards [selected_complete_symbolic_pattern_sum_eventually d Bs BD Bz hBs hBD hBz hk,
    HistoryBulkFixedReferenceTerm.selected_reference_equality_eventually d Bs BD Bz (by omega : 0<k)]
    with L hsum href
  intro E C hG hGu hcl hcu hb hd spectator hspec
  let hactual := href E C hG hcl hcu hb hd spectator hspec
  refine ⟨hactual,?_⟩
  intro outside hout hlen l hl
  obtain ⟨hV,hbound⟩ := hsum E C hG hGu hcl hcu hb hd spectator hspec outside hout hlen l hl
  refine ⟨hV,?_⟩
  intro mixed
  rw [selectedAggregate_eq_background]
  apply le_trans ((backgroundPrior C l).norm_cmean_le _)
  apply le_trans ((backgroundPrior C l).mean_mono (fun bg=>?_))
  · exact (backgroundPrior C l).mean_const _ |>.le
  · exact hbound (fun p b=>selectedFamily C outside hactual hl hout p
      (restoreOuterBackground C l p bg b) mixed) mixed

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
