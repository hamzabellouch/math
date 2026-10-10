import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySquareSeriesIntegral
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFiniteContourShift

namespace OAI

/-! # The original divisor coefficients in each shifted finite contour -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

 theorem density_LSeries_term_add (a : ℕ → ℂ) (s w : ℂ) (n : ℕ) :
    LSeries.term a (s + w) n = LSeries.term a s n / (n : ℂ) ^ w := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hnC]
    ring

 theorem densityFiniteKernel_original_terms (χ : PrimitiveComplexCharacter) (s w : ℂ)
    (S : Finset ℕ) :
    densityFiniteKernel χ s S (fun n => LSeries.term (densitySquareCoefficient χ) s n) w =
      ∑ n ∈ S, densitySquareKernel χ s w * LSeries.term (densitySquareCoefficient χ) (s + w) n := by
  unfold densityFiniteKernel densityFiniteMellin
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [density_LSeries_term_add]

 theorem densitySquareIntegralTerm_sum (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (S : Finset ℕ) :
    (∑ n ∈ S, densitySquareIntegralTerm χ s n) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ u : ℝ,
        densityFiniteKernel χ s S (fun n => LSeries.term (densitySquareCoefficient χ) s n) (1 + u * I) := by
  unfold densitySquareIntegralTerm
  rw [← Finset.mul_sum, ← integral_finsetSum S (fun n _ => densitySquareSeriesTerm_integrable χ s hs n)]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  exact (densityFiniteKernel_original_terms χ s (1 + u * I) S).symm

 theorem densitySquareIntegralTerm_sum_shift (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : s.re = 1 / 2) (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (∑ n ∈ S, densitySquareIntegralTerm χ s n) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ u : ℝ,
        densityFiniteKernel χ s S (fun n => LSeries.term (densitySquareCoefficient χ) s n)
          ((c : ℂ) + u * I) := by
  rw [densitySquareIntegralTerm_sum χ s hs S,
    densityFiniteKernel_shift χ s hs S (fun n => LSeries.term (densitySquareCoefficient χ) s n) hS c hc hc1]

end Ostmann

end OAI
