import OAI.NumberTheory.CubicMoment.Estimates.PrimeCoordinateErrors
import OAI.NumberTheory.CubicMoment.Estimates.PrimeIndicatorPowers

namespace OAI

/-! The exact normalized-prime discrepancy transfers second moments to
original prime-indicator convolutions. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeIndicator_moment_transfer {ρ : Type*} (P : Finset ρ)
    (a b : ρ → Eisenstein) (hab : ∀ r ∈ P, primary (a r) ∧ primary (b r))
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    (∑ r ∈ P, ‖primaryPrimeIndicatorTuple (a r) (b r) q η t W X V Y‖^2) ≤
      2*(∑ r ∈ P, ‖primaryNormalizedVonMangoldtTuple (a r) (b r) q η t W X V Y‖^2)+
      2*(∑ r ∈ P, ‖primeCoordinateError (a r) (b r) q η t W X V Y‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r hr
  apply norm_square_le_central_tail
  rw [norm_sub_rev,normalized_prime_tuple_difference (a r) (b r)
    (hab r hr).1 (hab r hr).2 q η t W X V hY hV]
  exact le_rfl

end CubicFirstMoment

end

end OAI
