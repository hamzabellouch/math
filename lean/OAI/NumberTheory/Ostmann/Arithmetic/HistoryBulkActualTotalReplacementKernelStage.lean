import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementKernelPoint
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementMean

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkActualBSquareReplacement HistoryBulkActualPrincipalBlockFamily

theorem selected_plain_kernel_stage_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
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
        (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (mixed : Bool),
      ‖plainKernelAverage C spectator D hl σ mixed false-
          plainKernelAverage C spectator D hl σ mixed true‖ ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖plainKernelAverage C spectator D hl σ mixed false-
          plainKernelAverage C spectator D hl σ mixed true‖ ≤
          Real.exp (-H*(bulkSize k L:ℝ)) :=
  (selected_plain_kernel_point_eventually d Bs BD Bz H hBs hH hk).mono
    (fun L h E C hG hGu hcl hcu hb hd spectator hspec l hl D σ mixed =>
      norm_cmean_sub_le_both (spectatorPrior spectator (2*(bulkSize k L/2)))
        (plainKernelValue C spectator D hl σ mixed false)
        (plainKernelValue C spectator D hl σ mixed true)
        (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
        (Real.exp (-H*(bulkSize k L:ℝ)))
        (fun ds _ => h E C hG hGu hcl hcu hb hd spectator hspec l hl D σ mixed ds))

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
