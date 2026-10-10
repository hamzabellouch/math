import OAI.NumberTheory.CubicMoment.Angular.AngularDivisorLogEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.PoissonTailSum

namespace OAI

/-! Infinite high-frequency summation for each actual divisor block. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_logarithmic_divisor_poisson_tail {R : ℝ} (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ (K : ℝ) (a : ℕ), 0 ≤ K ∧ ∀ (r : γ) (X : ι → ℝ),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      ∀ (A : ℝ) (d e : Eisenstein) (u : ℝ) (n : ℕ) (H : ℕ → Finset Eisenstein)
      (hd : d ≠ 0), 0 < A → (∀ j, H j ⊆ divisorFrequencyDyad d hd j) →
      let t := A/(27*(norm d)^3*(R^Fintype.card ι*L r)^2)
      Summable (fun j => finiteDivisorPoissonContribution d (fullSquarefreePrimeSupport R (W r) X e)
        (H (j+n)) (angularHeightPrimeCoefficient ℓ R (W r) X) u V A) ∧
      ‖∑' j : ℕ, finiteDivisorPoissonContribution d (fullSquarefreePrimeSupport R (W r) X e)
        (H (j+n)) (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        (K*(A/(norm d)^2)*L r*(1+Real.log (L r))^a/(t*(2:ℝ)^n)^m)*
          (t^(-3:ℝ)*((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹) := by
  obtain ⟨K,a,hK,hbound⟩ := angular_logarithmic_divisor_poisson_dyad ℓ hR hW hlo hhi V hV hV' (m+3)
  refine ⟨K,a,hK,?_⟩
  intro r X hL hX hprod A d e u n H hd hA hH
  dsimp only
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hdN : 0 < norm d := norm_pos_of_ne_zero hd
  have hz : 0 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  let t := A/(27*(norm d)^3*(R^Fintype.card ι*L r)^2)
  let C := K*(A/(norm d)^2)*L r*(1+Real.log (L r))^a
  let F := fun j => finiteDivisorPoissonContribution d (fullSquarefreePrimeSupport R (W r) X e)
    (H j) (angularHeightPrimeCoefficient ℓ R (W r) X) u V A
  have ht : 0 < t := by dsimp [t]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrow (j : ℕ) : ‖F j‖ ≤ C*(2:ℝ)^j/(1+t*(2:ℝ)^j)^(m+3) := by
    have heq : t*(2:ℝ)^j = A*(2:ℝ)^j/(27*(norm d)^3*(R^Fintype.card ι*L r)^2) := by
      dsimp [t]
      ring
    rw [heq]
    exact hbound r X hL hX hprod A d e u j (H j) hd hA (hH j)
  exact poisson_dyadic_tail ht hC m n F hrow

end CubicFirstMoment

end

end OAI
