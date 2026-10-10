import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamilyError

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryBulkPrincipalKernelReplacementMatched Filter
attribute [local instance] Classical.propDecidable
local instance actualCorrectedPrincipalSelectedInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_corrected_principal_factory_kernel_error_eventually
    (d : Decomposition) (Bs BD Bz D H : ℝ) {k : ℕ}
    (hBs : 0≤Bs)(hH : 0≤H)(hk : 0<k) :
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
      ∀outside : List ℕ,(∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q) →
      ∀(n : ℕ)(hlen : outside.length=2*n),outside.length≤bulkSize k L →
      ∀(l : ℕ), l<k →
      ∀(e : RemainingPermutation (k:=k) (L:=L) (l:=l))(he : PreservesRemainingBands (Template.remainder (l+1)
        (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e),
      ∃(hprime : ∀q∈outside,q.Prime)
        (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q),
      ∀mask : (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l) →
        (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l) →
        (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
        OriginalDraw (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p → Prop,
      Real.exp (D*(L+1)^2)*correctedKernelError (l:=l) C outside e he n hlen hprime hV mask≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      Real.exp (D*(L+1)^2)*correctedKernelError (l:=l) C outside e he n hlen hprime hV mask≤
          Real.exp (-H*(bulkSize k L:ℝ)) := by
  filter_upwards [HistoryBulkSupportConverse.selected_source_inputs_eventually d Bs BD Bz hk,
    selected_root_principal_kernel_error_eventually d Bs BD Bz D H hBs hH hk] with L hsource herror
  intro E C hG hGu hcl hcu hb hd spectator hspec outside houtside n hlen hsize l hl e he
  have hsf := (hsource E C hG hcl hcu hb hd spectator hspec).2.2
  have hprime : ∀q∈outside,q.Prime := by
    intro q hq
    obtain ⟨r,rfl⟩ := houtside q hq
    exact spectator.prime r.val r.property
  have hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q := by
    intro q hq j hj
    obtain ⟨r,rfl⟩ := houtside q hq
    exact hsf r j (hj.trans (Nat.le_of_lt hl))
  refine ⟨hprime,hV,?_⟩
  intro mask
  have hlog : ∀q∈outside,Real.log (q:ℝ)≤Real.exp ((1/1000:ℝ)*L) := by
    intro q hq
    obtain ⟨r,rfl⟩ := houtside q hq
    exact (hspec r).2
  exact herror E C hG hGu hcl hcu hb hd spectator hspec l true true hl
    outside (fun q hq=>(hprime q hq).pos) hsize hlog
    (fun v f g p=>correctedPrincipalFamily (l:=l) C p outside e he n hlen hprime hV v f g)
    (fun v f g p o ho=>correctedPrincipalFamily_reference_giants (l:=l) C p outside e he n hlen hprime hV
      v f g o ho) mask

end Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamily

end

end OAI
