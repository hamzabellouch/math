import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedIndexFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedLawsBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximationReference
open HistoryGiantReferenceMean Filter
attribute [local instance] Classical.propDecidable
local instance selectedKernelLawsIndexInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_law_kernel_index_errors_eventually (d : Decomposition)
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
        (Jprime Jmixed : (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) →
          OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p →
          Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
          SelectedBulkSample C l → ℤ → ℤ → ℂ),
      let Sp := fun symbolic =>
        ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,
          primeKernelMean C p outside σ (Jprime p) hactual hl houtside hlen hprime hV
            i.1 i.2.1 i.2.2 symbolic
      let Sm := fun symbolic =>
        ∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,
          mixedKernelMean C p outside σ (Jmixed p) hactual hl houtside hlen hprime hV
            i.1 i.2.1 i.2.2 symbolic
      (‖Sp false-Sp true‖≤Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
        ‖Sp false-Sp true‖≤Real.exp (-H*(bulkSize k L:ℝ))) ∧
      (‖Sm false-Sm true‖≤Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
        ‖Sm false-Sm true‖≤Real.exp (-H*(bulkSize k L:ℝ))) :=
  (selected_law_kernel_sum_errors_eventually d Bs BD Bz H hBs hH hk).mono
    (fun L h E C hG hGu hcl hcu hb hd spectator hspec =>
      (h E C hG hGu hcl hcu hb hd spectator hspec).elim (fun hactual h =>
        ⟨hactual,fun outside houtside hlen l hl =>
          (h outside houtside hlen l hl).elim (fun hprime h => h.elim (fun hV h =>
            ⟨hprime,hV,fun σ Jprime Jmixed =>
              ⟨four_sum_bounds_to_index
                (fun v f g p => primeKernelMean C p outside σ (Jprime p) hactual hl houtside hlen hprime hV v f g false)
                (fun v f g p => primeKernelMean C p outside σ (Jprime p) hactual hl houtside hlen hprime hV v f g true)
                (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
                (Real.exp (-H*(bulkSize k L:ℝ))) (h σ Jprime Jmixed).1,
               four_sum_bounds_to_index
                (fun v f g p => mixedKernelMean C p outside σ (Jmixed p) hactual hl houtside hlen hprime hV v f g false)
                (fun v f g p => mixedKernelMean C p outside σ (Jmixed p) hactual hl houtside hlen hprime hV v f g true)
                (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
                (Real.exp (-H*(bulkSize k L:ℝ))) (h σ Jprime Jmixed).2⟩⟩))⟩))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end

end OAI
