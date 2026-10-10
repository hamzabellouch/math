import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Line

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set

namespace OrdinaryHorizontalHalasz
lemma derivative_vertical_bounded {f : ℕ → ℂ} (hf : ∀n, ‖f n‖≤1)
    {δ : ℝ} (hδ : 0<δ) : ∃B : ℝ, ∀t : ℝ, ‖deriv (LSeries f) (line δ t)‖≤B := by
  have hab : LSeries.abscissaOfAbsConv f≤(1:ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1,fun n _ => hf n⟩
  have hlog := (LSeriesSummable_logMul_of_lt_re (lt_of_le_of_lt hab
    (by exact_mod_cast (show 1<(line δ 0).re by simp; linarith)))).norm
  refine ⟨∑'n, ‖LSeries.term (LSeries.logMul f) (line δ 0) n‖,?_⟩
  intro t
  rw [LSeries_deriv (lt_of_le_of_lt hab (by exact_mod_cast (show 1<(line δ t).re by simp; linarith))),norm_neg]
  have he (n : ℕ) : ‖LSeries.term (LSeries.logMul f) (line δ t) n‖=
      ‖LSeries.term (LSeries.logMul f) (line δ 0) n‖ := by
    rw [LSeries.norm_term_eq,LSeries.norm_term_eq]
    simp
  exact (norm_tsum_le_tsum_norm (hlog.congr (fun n => (he n).symm))).trans_eq (tsum_congr he)
end OrdinaryHorizontalHalasz

end

end OAI
