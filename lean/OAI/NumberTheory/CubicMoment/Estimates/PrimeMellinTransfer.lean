import OAI.NumberTheory.CubicMoment.Estimates.PrimeSharpCutoff
import OAI.NumberTheory.CubicMoment.Estimates.MellinWeightBounds

namespace OAI

/-!
# The prime comparison through a common-height integral

The angular Gauss-minus-model coefficients are uniformly bounded. The
actual sharp dyadic prime sum differs negligibly from the same finite
polynomial integrated against the constructed Mellin cutoff.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def primeComparisonCoefficient (ℓ : ℤ) (p : Eisenstein) : ℂ :=
  theta ℓ p * (gaussAtPrime p - ((cStar*norm p^(-1/6 : ℝ) : ℝ) : ℂ))

lemma primeComparisonCoefficient_bound (ℓ : ℤ) {p : Eisenstein} (hp : primaryPrime p) :
    ‖primeComparisonCoefficient ℓ p‖ ≤ 1+cStar := by
  have hg : ‖gaussAtPrime p‖ = 1 := by
    rw [← gauss_prime hp]
    exact norm_gauss_of_squarefree hp.1 hp.2.squarefree
  have hw : norm p^(-1/6 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_norm hp.2.ne_zero) (by norm_num)
  have hmodel : ‖((cStar*norm p^(-1/6 : ℝ) : ℝ) : ℂ)‖ ≤ cStar := by
    rw [Complex.norm_real,Real.norm_of_nonneg (mul_nonneg cStar_pos.le (Real.rpow_nonneg (norm_nonneg p) _))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hw cStar_pos.le
  rw [primeComparisonCoefficient,norm_theta_mul hp.2.ne_zero]
  exact (norm_sub_le _ _).trans (by rw [hg]; linarith)

def sharpDyadicPrimeComparison (ℓ : ℤ) (X : ℝ) : ℂ :=
  ∑ p ∈ primeCutoff (4*X), primeComparisonCoefficient ℓ p*(intervalStep X (2*X) (norm p) : ℝ)

def smoothedDyadicPrimeComparison (ℓ : ℤ) (ρ X : ℝ) : ℂ :=
  ∑ p ∈ primeCutoff (4*X), primeComparisonCoefficient ℓ p*
    smoothLogInterval (X^(1/6+ρ : ℝ)) (norm p/X)

def comparisonMellinIntegral (ℓ : ℤ) (ρ X : ℝ) : ℂ :=
  ∫ ξ : ℝ, truncatedMellinWeight X (X^(1/6+ρ : ℝ)) ξ *
    (∑ p ∈ primeCutoff (4*X), primeComparisonCoefficient ℓ p*normTwist (2*Real.pi*ξ) p)

lemma smoothedDyadicPrimeComparison_eq_integral (ℓ : ℤ) (ρ : ℝ)
    {X : ℝ} (hX : 0 < X) :
    smoothedDyadicPrimeComparison ℓ ρ X = comparisonMellinIntegral ℓ ρ X := by
  exact smoothed_polynomial_eq_mellin (primeCutoff (4*X)) (primeComparisonCoefficient ℓ)
    hX (Real.rpow_pos_of_pos hX _) (fun p hp => (mem_primeCutoff.mp hp).1.2.ne_zero)

lemma sharpDyadicPrimeComparison_sub_smooth (ℓ : ℤ) (ρ X : ℝ) :
    sharpDyadicPrimeComparison ℓ X - smoothedDyadicPrimeComparison ℓ ρ X =
      ∑ p ∈ primeCutoff (4*X), primeComparisonCoefficient ℓ p*
        sharpIntervalError X (X^(1/6+ρ : ℝ)) (norm p) := by
  simp only [sharpDyadicPrimeComparison,smoothedDyadicPrimeComparison,
    sharpIntervalError,mul_sub,Finset.sum_sub_distrib]

/-- The exact inverse-transform integral approximates the actual angular
Gauss-minus-model prime sum at the required first-moment scale. -/
theorem sharpDyadicPrimeComparison_sub_integral_isLittleO (ℓ : ℤ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 5/6) :
    (fun X : ℝ => sharpDyadicPrimeComparison ℓ X - comparisonMellinIntegral ℓ ρ X)
      =o[Filter.atTop] firstMomentScale := by
  have h := prime_sharp_interval_error_isLittleO hρ hρ₁
    (show 0 ≤ 1+cStar from by linarith [cStar_pos])
    (fun X => primeCutoff (4*X)) (fun _ => primeComparisonCoefficient ℓ)
    (fun X _ p hp => mem_primeCutoff.mp hp)
    (fun X _ p hp => primeComparisonCoefficient_bound ℓ (mem_primeCutoff.mp hp).1)
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with X hX
  rw [← sharpDyadicPrimeComparison_sub_smooth,smoothedDyadicPrimeComparison_eq_integral ℓ ρ hX]

end CubicFirstMoment

end

end OAI
