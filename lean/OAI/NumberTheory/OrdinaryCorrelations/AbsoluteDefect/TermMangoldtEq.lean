import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.FourierSeries
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Complete

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

namespace OrdinaryDirichletMeanSquare
open OrdinaryLogDerivative

lemma term_mangoldt_eq (f : ℕ → ℂ) (δ t : ℝ) (n : ℕ) :
    LSeries.term (mangoldtTwist f) ((1+δ : ℝ) - (t:ℂ)*Complex.I) n =
      mangoldtCoefficient f δ n * phase (Real.log n) t := by
  by_cases hn : n=0
  · simp [hn,LSeries.term_def,mangoldtCoefficient]
  · rw [LSeries.term_of_ne_zero hn,
      Complex.cpow_def_of_ne_zero (show (n:ℂ)≠0 by exact_mod_cast hn)]
    rw [←Complex.ofReal_natCast,←Complex.ofReal_log (Nat.cast_nonneg n)]
    simp only [div_eq_mul_inv,←Complex.exp_neg,mangoldtTwist,mangoldtCoefficient,
      phase,Complex.ofReal_mul,Complex.ofReal_exp]
    simp only [mul_assoc,←Complex.exp_add]
    congr 2
    push_cast
    ring_nf

lemma mangoldt_LSeries_eq (f : ℕ → ℂ) (δ t : ℝ) :
    LSeries (mangoldtTwist f) ((1+δ : ℝ) - (t:ℂ)*Complex.I) =
      fourierSeries (mangoldtCoefficient f δ) (fun n => Real.log n) t := by
  apply tsum_congr
  exact term_mangoldt_eq f δ t

theorem mangoldt_LSeries_gaussian_energy (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖≤1)
    {δ : ℝ} (hδ : 0<δ) :
    (∫ t : ℝ, gaussian t *
      ‖LSeries (mangoldtTwist f) ((1+δ : ℝ) - (t:ℂ)*Complex.I)‖^2) ≤
      gaussianConstant * Real.exp 3 * 4 *
        (chebyshevConstant * Real.exp 1)^2 * (2+1/δ) := by
  simpa only [mangoldt_LSeries_eq] using mangoldt_series_gaussian_energy f hf hδ

end OrdinaryDirichletMeanSquare

end

end OAI
