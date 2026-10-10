import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelected
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
local instance selectedKernelLawsInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_law_kernel_sum_errors_eventually (d : Decomposition)
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
      let Sp := fun symbolic => ∑v,∑f,∑g,∑p,
        primeKernelMean C p outside σ (Jprime p) hactual hl houtside hlen hprime hV v f g symbolic
      let Sm := fun symbolic => ∑v,∑f,∑g,∑p,
        mixedKernelMean C p outside σ (Jmixed p) hactual hl houtside hlen hprime hV v f g symbolic
      (‖Sp false-Sp true‖≤Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
        ‖Sp false-Sp true‖≤Real.exp (-H*(bulkSize k L:ℝ))) ∧
      (‖Sm false-Sm true‖≤Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
        ‖Sm false-Sm true‖≤Real.exp (-H*(bulkSize k L:ℝ))) :=
  (selected_kernel_sum_errors_eventually d Bs BD Bz H hBs hH hk).mono
    (fun _L h E C hG hGu hcl hcu hb hd spectator hspec =>
      (h E C hG hGu hcl hcu hb hd spectator hspec).elim (fun hactual h =>
        ⟨hactual,fun outside houtside hlen l hl =>
          (h outside houtside hlen l hl).elim (fun hprime h => h.elim (fun hV h =>
            ⟨hprime,hV,fun σ Jprime Jmixed =>
              ⟨h σ Jprime (PrimeDraw C.giant)
                (primeWeight C.giant) (primeP C.giant) (primeQ C.giant)
                (primeWeight_nonneg C.giant) (fun r _ => primeDraw_positive C.giant r)
                (fun r hr => prime_draw_cells C r
                  (lt_of_le_of_ne (primeWeight_nonneg C.giant r) (Ne.symm hr))) false false hl,
               h σ Jmixed (MixedDraw C.giantCenter C.giant)
                (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant)
                (mixedQ C.giantCenter C.giant) (mixedWeight_nonneg C.giantCenter C.giant)
                (fun r _ => mixedDraw_positive C.giantCenter C.giant r)
                (fun r hr => mixed_draw_cells C r
                  (lt_of_le_of_ne (mixedWeight_nonneg C.giantCenter C.giant r) (Ne.symm hr))) false true hl⟩⟩))⟩))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end

end OAI
