import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedSquarePoint
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementMean

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkActualBSquareReplacement HistoryBulkActualPrincipalBlockFamily
open HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable

theorem selected_corrected_square_stage_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
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
        (e : RemainingPermutation (k:=k) (L:=L) (l:=l)),
      ‖correctedSquareAverage C spectator D hl e false-
          correctedSquareAverage C spectator D hl e true‖ ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖correctedSquareAverage C spectator D hl e false-
          correctedSquareAverage C spectator D hl e true‖ ≤
          Real.exp (-H*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_corrected_square_point_eventually d Bs BD Bz H hBs hH hk] with L h
  intro E C hG hGu hcl hcu hb hd spectator hspec l hl D e
  by_cases he : PreservesRemainingBands _ e
  · simp only [correctedSquareAverage,dite_eq_left he]
    exact norm_cmean_sub_le_both (spectatorPrior spectator (2*(bulkSize k L/2)))
      (correctedSquareValue C spectator D hl e he false)
      (correctedSquareValue C spectator D hl e he true)
      (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
      (Real.exp (-H*(bulkSize k L:ℝ)))
      (fun ds _ => h E C hG hGu hcl hcu hb hd spectator hspec l hl D e he ds)
  · simp only [correctedSquareAverage,dite_eq_right he,sub_self,norm_zero]
    exact ⟨(Real.exp_pos _).le,(Real.exp_pos _).le⟩

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
