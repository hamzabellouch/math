import OAI.NumberTheory.CubicMoment.Angular.AngularSquarefreeCoordinateErrors
import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeMomentTransfer

namespace OAI

/-! The exact angular squarefree discrepancy transfers moments to the
squarefree prime coefficient, with the original product cutoff retained. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma angular_squarefreePrime_moment_transfer {ρ : Type*} (P : Finset ρ)
    (ℓ : ℤ) (a b : ρ → Eisenstein) (hab : ∀ r ∈ P, primary (a r) ∧ primary (b r))
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    (∑ r ∈ P, ‖primaryAngularSquarefreePrimeTuple ℓ (a r) (b r) q η t W X V Y‖^2) ≤
      2*(∑ r ∈ P, ‖primaryAngularPrimeIndicatorTuple ℓ (a r) (b r) q η t W X V Y‖^2)+
      2*(∑ r ∈ P, ‖angularSquarefreeCoordinateError ℓ (a r) (b r) q η t W X V Y‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r hr
  apply norm_square_le_central_tail
  rw [norm_sub_rev,angular_primeIndicator_sub_squarefree_cutoff ℓ (a r) (b r)
    (hab r hr).1 (hab r hr).2 q η t W X V hY hV]

end CubicFirstMoment

end

end OAI
