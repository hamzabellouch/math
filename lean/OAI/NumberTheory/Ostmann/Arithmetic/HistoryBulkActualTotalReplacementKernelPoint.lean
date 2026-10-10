import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedLawsIndex
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementKernelDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkActualBSquareReplacement HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualPrincipalKernelStage

theorem selected_plain_kernel_point_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀ p : spectator.Sample, Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℕ) ∧
        Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀ (l : ℕ) (hl : l ≤ k) (D : PlainStageData C spectator l)
        (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (mixed : Bool)
        (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample),
      ‖plainKernelValue C spectator D hl σ mixed false ds-
          plainKernelValue C spectator D hl σ mixed true ds‖ ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖plainKernelValue C spectator D hl σ mixed false ds-
          plainKernelValue C spectator D hl σ mixed true ds‖ ≤
          Real.exp (-H*(bulkSize k L:ℝ)) :=
  (selected_law_kernel_index_errors_eventually d Bs BD Bz H hBs hH hk).mono
    (fun _L h E C hG hGu hcl hcu hb hd spectator hspec l hl _D σ mixed ds =>
      (h E C hG hGu hcl hcu hb hd spectator hspec).elim (fun _hactual h =>
        (h (spectatorList spectator ds)
          (fun _q hq => (List.mem_ofFn.mp hq).elim (fun i hi => ⟨ds i,hi⟩))
          List.length_ofFn l hl).elim (fun _hp h => h.elim (fun _hV h =>
            let hs := h σ
              (fun p o => primeLawMultiplier C (outerGiants C l p o,outerNonbulk C l p o))
              (fun p o => plainMixedLawMultiplier C (spectatorList spectator ds)
                (outerGiants C l p o,outerNonbulk C l p o))
            Bool.rec hs.1 hs.2 mixed))))

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
