import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementCorrectedSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedSquareDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkActualBSquareReplacement HistoryBulkActualPrincipalBlockFamily
open HistoryBulkIndependentFibreReference

theorem selected_corrected_square_point_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 2 ≤ k) :
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
      ∀ (l : ℕ) (hl : l<k) (D : PlainStageData C spectator l)
        (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
        (he : PreservesRemainingBands _ e)
        (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample),
      ‖correctedSquareValue C spectator D hl e he false ds-
          correctedSquareValue C spectator D hl e he true ds‖ ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖correctedSquareValue C spectator D hl e he false ds-
          correctedSquareValue C spectator D hl e he true ds‖ ≤
          Real.exp (-H*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_corrected_errors_eventually d Bs BD Bz H hBs hH hk] with L h
  intro E C hG hGu hcl hcu hb hd spectator hspec l hl D e he ds
  obtain ⟨hp,hAd,hV,hbound⟩ := h E C hG hGu hcl hcu hb hd spectator hspec
    (spectatorList spectator ds)
    (fun _q hq => (List.mem_ofFn.mp hq).elim (fun i hi => ⟨ds i,hi⟩))
    List.length_ofFn l hl
  exact (hbound e he).2

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
