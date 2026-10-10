import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszPrimeGram
import Mathlib.NumberTheory.LSeries.Dirichlet

namespace OAI

/-! The positive quadratic Riesz prime majorant is exactly an integral
of the logarithmic derivative of zeta. No cutoff is moved or rounded. -/

namespace TwoPointCorrelations

open Complex MeasureTheory _root_.Erdos970 _root_.OAI.Erdos970 Finset ArithmeticFunction
open scoped Classical

noncomputable def mrtMangoldtTwist (u : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((u : ℂ) * Complex.I))

noncomputable def mrtZetaRieszIntegrand (x u : ℝ) (s : ℂ) : ℂ :=
  (-deriv riemannZeta (s + (u : ℂ) * Complex.I) /
    riemannZeta (s + (u : ℂ) * Complex.I)) * mrtRieszKernel x s

lemma mrt_mangoldt_twist_term (u : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (mrtMangoldtTwist u) s n =
      LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (s + (u : ℂ) * Complex.I) n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      mrtMangoldtTwist, Complex.cpow_neg, Complex.cpow_add _ _ hnC]
    ring

lemma mrt_mangoldt_twist_summable (u : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (mrtMangoldtTwist u) s := by
  have ht : 1 < (s + (u : ℂ) * Complex.I).re := by simpa using hs
  exact (LSeriesSummable_vonMangoldt ht).congr (fun n => (mrt_mangoldt_twist_term u s n).symm)

lemma mrt_mangoldt_twist_LSeries (u : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (mrtMangoldtTwist u) s =
      -deriv riemannZeta (s + (u : ℂ) * Complex.I) /
        riemannZeta (s + (u : ℂ) * Complex.I) := by
  rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs)]
  exact tsum_congr (mrt_mangoldt_twist_term u s)

lemma mrt_mangoldt_twist_phase (u : ℝ) {n : ℕ} (hn : n ≠ 0) :
    mrtMangoldtTwist u n = (ArithmeticFunction.vonMangoldt n : ℂ) *
      Complex.exp (((-Real.log (n : ℝ) * u : ℝ) : ℂ) * Complex.I) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  unfold mrtMangoldtTwist
  rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg n)]
  congr 2
  push_cast
  ring

theorem mrt_riesz_mangoldt_finite_sum {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) (u : ℝ) :
    VerticalIntegral' (mrtZetaRieszIntegrand x u) σ =
      ∑ n ∈ Icc 1 ⌊x⌋₊, mrtMangoldtTwist u n * mrtRieszSquare ((n : ℝ) / x) := by
  have he := mrt_riesz_finite_sum (mrtMangoldtTwist u) hx (by linarith : 1 / 2 ≤ σ)
    (mrt_mangoldt_twist_summable u (by simpa using hσ))
  unfold VerticalIntegral' VerticalIntegral
  unfold VerticalIntegral' VerticalIntegral at he
  rw [← he]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with t
  rw [mrtZetaRieszIntegrand, mrt_mangoldt_twist_LSeries u (by simpa using hσ)]

theorem mrt_riesz_prime_kernel_integral {Y σ : ℝ} (hY : 0 < Y) (hσ : 1 < σ) (u : ℝ) :
    mrtExponentialPolynomial (mrtRieszPrimeSupport Y)
      (fun n => (mrtRieszPrimeWeight Y n * ArithmeticFunction.vonMangoldt n : ℝ))
      (fun n => -Real.log (n : ℝ)) u =
        4 * VerticalIntegral' (mrtZetaRieszIntegrand (4 * Y) u) σ := by
  rw [mrt_riesz_mangoldt_finite_sum (by positivity) hσ]
  unfold mrtExponentialPolynomial mrtRieszPrimeSupport
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [mrt_mangoldt_twist_phase u (by have h := (mem_Icc.mp hn).1; omega)]
  unfold mrtRieszPrimeWeight mrtRieszSquare
  push_cast
  ring

end TwoPointCorrelations

end OAI
