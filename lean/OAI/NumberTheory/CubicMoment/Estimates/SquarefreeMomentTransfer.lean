import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeCoordinateErrors
import OAI.NumberTheory.CubicMoment.Estimates.PrimeIndicatorPowers

namespace OAI

/-! The exact squarefree discrepancy transfers prime moments to
the squarefree coefficient in the manuscript. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma squarefreePrime_moment_transfer {ρ : Type*} (P : Finset ρ)
    (a b : ρ → Eisenstein) (hab : ∀ r ∈ P, primary (a r) ∧ primary (b r))
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    (∑ r ∈ P, ‖primarySquarefreePrimeTuple (a r) (b r) q η t W X V Y‖^2) ≤
      2*(∑ r ∈ P, ‖primaryPrimeIndicatorTuple (a r) (b r) q η t W X V Y‖^2)+
      2*(∑ r ∈ P, ‖squarefreeCoordinateError (a r) (b r) q η t W X V Y‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r hr
  apply norm_square_le_central_tail
  rw [norm_sub_rev,primeIndicator_sub_squarefree_cutoff (a r) (b r)
    (hab r hr).1 (hab r hr).2 q η t W X V hY hV]
  exact le_rfl

lemma first_squarefree_error_rows {Y N κ c : ℝ} (hY : 1 ≤ Y) (hc : 0 < c)
    (hκ : κ ≤ c/256) (hN : N ≤ Y^(1+κ)) (a : Eisenstein) (ha : gramDyad N a) :
    primary a ∧ Squarefree a ∧ norm a ≤ (2*Y)^(1+c/32) := by
  have hp := first_prime_error_rows hY hc hκ hN a ha
  exact ⟨hp.1,hp.2.1,hp.2.2.trans
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))⟩

lemma balanced_squarefree_error_rows {Y κ c : ℝ} (hY : 1 ≤ Y) (hc : 0 < c)
    (hκ : κ ≤ c/256) (a : Eisenstein × Eisenstein)
    (ha : PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
      norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) :
    PrimarySquarefreePair a ∧ norm a.1 ≤ (2*Y)^(1/3+c/32) ∧
      norm a.2 ≤ (2*Y)^(1/3+c/32) := by
  have hp := balanced_prime_error_rows hY hc hκ a ha
  have he : (2*Y)^(1/3+c/256) ≤ (2*Y)^(1/3+c/32) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  exact ⟨hp.1,hp.2.1.trans he,hp.2.2.trans he⟩

end CubicFirstMoment

end

end OAI
