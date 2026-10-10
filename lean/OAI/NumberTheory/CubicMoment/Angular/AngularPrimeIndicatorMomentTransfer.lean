import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeCoordinateErrors
import OAI.NumberTheory.CubicMoment.Estimates.PrimeIndicatorPowers

namespace OAI

/-! The exact angular prime discrepancy transfers normalized prime
moments to the literal prime-indicator tuples. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma angular_primeIndicator_moment_transfer {ρ : Type*} (P : Finset ρ)
    (ℓ : ℤ) (a b : ρ → Eisenstein) (hab : ∀ r ∈ P, primary (a r) ∧ primary (b r))
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    (∑ r ∈ P, ‖primaryAngularPrimeIndicatorTuple ℓ (a r) (b r) q η t W X V Y‖^2) ≤
      2*(∑ r ∈ P, ‖primaryAngularCoefficientTuple ℓ
        (fun n => (normalizedVonMangoldt n:ℂ)) (a r) (b r) q η t W X V Y‖^2)+
      2*(∑ r ∈ P, ‖angularPrimeCoordinateError ℓ (a r) (b r) q η t W X V Y‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r hr
  apply norm_square_le_central_tail
  rw [norm_sub_rev,angular_normalized_prime_tuple_difference ℓ (a r) (b r)
    (hab r hr).1 (hab r hr).2 q η t W X V hY hV]

end CubicFirstMoment

end

end OAI
