import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasSelectionActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Preliminaries Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def balancedBoundedPrimes (d : Decomposition) (Q : ℕ)
    (P : Finset (PrimeUpTo Q)) : Finset (PrimeUpTo Q) :=
  P.filter (fun p => 1 / 3 ≤ d.residueDensity p.val ∧ d.residueDensity p.val ≤ 2 / 3)

theorem eventually_balanced_prime_weight (d : Decomposition) :
    ∀ᶠ X : ℕ in atTop, ∀ P : Finset (PrimeUpTo (collisionScale 4 X)),
      boundedPrimeWeight P ≤
        boundedPrimeWeight (balancedBoundedPrimes d (collisionScale 4 X) P) +
          3 * collisionConstant 4 * Real.log (Real.log (X : ℝ)) := by
  classical
  filter_upwards [eventually_upperWindow_density_stability d,
    eventually_collision_bound_conditions 4] with X hden hcond
  intro P
  let Q := collisionScale 4 X
  let w : PrimeUpTo Q → ℝ := fun p => Real.log p.val / p.val
  let σ : PrimeUpTo Q → ℝ := fun p => d.residueDensity p.val
  let E := collisionConstant 4 * Real.log (Real.log (X : ℝ))
  have hE : 0 ≤ E := mul_nonneg (collisionConstant_pos 4).le (by linarith [hcond.2.2.1])
  have hw : ∀ p : PrimeUpTo Q, 0 ≤ w p := bounded_prime_weight_nonneg
  have hfull : (∑ p : PrimeUpTo Q, w p * (σ p - 1 / 2) ^ 2) ≤ E / 16 := by
    simpa only [w, σ, E, div_mul_eq_mul_div] using hden
  have hsub := (sum_subset_univ_nonneg P (fun p => w p * (σ p - 1 / 2) ^ 2)
    (fun p => mul_nonneg (hw p) (sq_nonneg _))).trans hfull
  have hdel := goodBiasApproximation_weight P w σ (fun _ => 0) (fun _ => 0)
    (by norm_num : (0 : ℝ) < 1) (fun p _ => hw p)
  norm_num [GoodBiasApproximation] at hdel
  change boundedPrimeWeight P ≤ boundedPrimeWeight (balancedBoundedPrimes d Q P) + _
  change (∑ p ∈ P, w p) ≤ (∑ p ∈ P with 1 / 3 ≤ σ p ∧ σ p ≤ 2 / 3, w p) + _
  have h : (∑ p ∈ P, w p) ≤
      (∑ p ∈ P with 1 / 3 ≤ σ p ∧ σ p ≤ 2 / 3, w p) + 3 * E := by linarith
  simpa only [E, mul_assoc] using h

end Ostmann.QuadraticCenter

end

end OAI
