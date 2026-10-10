import Mathlib.MeasureTheory.Integral.DominatedConvergence
import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySquareTerms

namespace OAI

/-! # Exchanging the actual divisor series and the Gaussian contour integral -/

namespace Ostmann

open Complex MeasureTheory

 theorem densitySquareSeriesTerm_integral_summable (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖densitySquareSeriesTerm χ s n u‖) := by
  let K := Real.exp (2 * (59 + |Real.eulerMascheroniConstant|) + 4 +
    2 * (59 + |Real.eulerMascheroniConstant|) ^ 2) * ((χ.modulus : ℝ) * (|s.im| + 2))
  let g : ℝ → ℝ := fun u => Real.exp (-(u ^ 2) / 2)
  have hg : Integrable g := by
    convert integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) using 1
    funext u
    dsimp [g]
    congr 1
    ring
  have hb (n : ℕ) : (∫ u : ℝ, ‖densitySquareSeriesTerm χ s n u‖) ≤
      (K * ‖LSeries.term (densitySquareCoefficient χ) (3 / 2 : ℂ) n‖) * ∫ u : ℝ, g u := by
    rw [← integral_const_mul]
    apply integral_mono_ae (densitySquareSeriesTerm_integrable χ s hs n).norm
      (hg.const_mul _)
    filter_upwards with u
    exact densitySquareSeriesTerm_bound χ s hs n u
  have hsum := ((densitySquareCoefficient_summable χ).norm.mul_left K).mul_right (∫ u : ℝ, g u)
  exact hsum.of_nonneg_of_le (fun n => integral_nonneg (fun u => norm_nonneg _)) hb

noncomputable def densitySquareIntegralTerm (χ : PrimitiveComplexCharacter) (s : ℂ) (n : ℕ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ u : ℝ, densitySquareSeriesTerm χ s n u

 theorem densitySmoothedSquare_series (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) : densitySmoothedSquare χ s = ∑' n : ℕ, densitySquareIntegralTerm χ s n := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have he (u : ℝ) : densitySquareKernel χ s (1 + u * I) * χ.L (s + (1 + u * I)) ^ 2 =
      ∑' n : ℕ, densitySquareSeriesTerm χ s n u := by
    have hp : 1 < (s + (1 + (u : ℂ) * I)).re := by norm_num [hs]
    have hL : χ.L (s + (1 + u * I)) ^ 2 =
        LSeries (densitySquareCoefficient χ) (s + (1 + u * I)) :=
      (density_square_LSeries χ.character _ hp).symm
    rw [hL, LSeries, ← tsum_mul_left]
    rfl
  rw [densitySmoothedSquare_integral χ s hs]
  simp_rw [he]
  rw [← integral_tsum_of_summable_integral_norm (fun n => densitySquareSeriesTerm_integrable χ s hs n)
    (densitySquareSeriesTerm_integral_summable χ s hs)]
  exact tsum_mul_left.symm

end Ostmann

end OAI
