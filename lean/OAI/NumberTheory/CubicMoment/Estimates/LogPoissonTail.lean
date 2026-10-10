import OAI.NumberTheory.CubicMoment.Estimates.LogPoissonEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.PoissonTailSum

namespace OAI

/-! The genuine high-frequency Poisson tail with an arbitrary fixed
number of powers of decay past its lower endpoint. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem logarithmic_poisson_tail {R : ℝ} (hR : 1 ≤ R)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ (K : ℝ) (a : ℕ), 0 ≤ K ∧ ∀ (r : γ) (X : ι → ℝ),
      1 ≤ L r → (∀ i, 1 ≤ X i) → (∏ i, X i) = L r →
      ∀ (A : ℝ) (e : Eisenstein) (u : ℝ) (n : ℕ) (H : ℕ → Finset Eisenstein),
      0 < A → (∀ j, H j ⊆ frequencyDyad j) →
      let t := A/(27*(R^Fintype.card ι*L r)^2)
      Summable (fun j => finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e)
        (H (j+n)) (fullPrimeCoefficient R (W r) X) u V A) ∧
      ‖∑' j : ℕ, finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e)
        (H (j+n)) (fullPrimeCoefficient R (W r) X) u V A‖ ≤
        (K*A*L r*(1+Real.log (L r))^a/(t*(2:ℝ)^n)^m)*
          (t^(-3:ℝ)*((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹) := by
  obtain ⟨K,a,hK,hbound⟩ := logarithmic_absolute_poisson_dyad hR hW hlo hhi V hV hV' (m+3)
  refine ⟨K,a,hK,?_⟩
  intro r X hL hX hprod A e u n H hA hH
  dsimp only
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 ≤ 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  let t := A/(27*(R^Fintype.card ι*L r)^2)
  let C := K*A*L r*(1+Real.log (L r))^a
  let F := fun j => finitePoissonContribution (fullSquarefreePrimeSupport R (W r) X e)
    (H j) (fullPrimeCoefficient R (W r) X) u V A
  have ht : 0 < t := by dsimp [t]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrow (j : ℕ) : ‖F j‖ ≤ C*(2:ℝ)^j/(1+t*(2:ℝ)^j)^(m+3) := by
    have heq : t*(2:ℝ)^j = A*(2:ℝ)^j/(27*(R^Fintype.card ι*L r)^2) := by
      dsimp [t]
      ring
    rw [heq]
    exact hbound r X hL hX hprod A e u j (H j) hA (hH j)
  exact poisson_dyadic_tail ht hC m n F hrow

end CubicFirstMoment

end

end OAI
