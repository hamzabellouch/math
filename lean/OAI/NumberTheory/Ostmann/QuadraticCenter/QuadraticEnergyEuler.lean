import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticEnergyArray

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem reciprocalSqrtDivisorSum_eq_euler {L : ℕ} (hL : Squarefree L) :
    reciprocalSqrtDivisorSum L = ∏ p ∈ L.primeFactors, (1+(Real.sqrt (p : ℝ))⁻¹) := by
  classical
  unfold reciprocalSqrtDivisorSum
  rw [sum_squarefree_divisors_eq_cube hL]
  simp_rw [sqrt_primeSubsetProduct, ← Finset.prod_inv_distrib]
  calc
    _ = ∏ p : L.primeFactors, (1+(Real.sqrt (p.val : ℝ))⁻¹) := by
      simpa only [Finset.powerset_univ] using
        (Finset.prod_one_add (f := fun p : L.primeFactors => (Real.sqrt (p.val : ℝ))⁻¹)
          Finset.univ).symm
    _ = _ := Finset.prod_coe_sort L.primeFactors (fun p : ℕ => 1+(Real.sqrt (p : ℝ))⁻¹)

theorem reciprocalSqrtDivisorSum_le_exp {L : ℕ} (hL : Squarefree L)
    {z : ℝ} (hz : 0 < z) (hprimes : ∀ p ∈ L.primeFactors, z ≤ (p : ℝ)) :
    reciprocalSqrtDivisorSum L ≤ Real.exp ((L.primeFactors.card : ℝ)/Real.sqrt z) := by
  rw [reciprocalSqrtDivisorSum_eq_euler hL]
  apply (Real.prod_one_add_le_exp_sum L.primeFactors
    (f := fun p : ℕ => (Real.sqrt (p : ℝ))⁻¹) (fun p => by positivity)).trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ∑ _p ∈ L.primeFactors, (Real.sqrt z)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact inv_anti₀ (Real.sqrt_pos.mpr hz) (Real.sqrt_le_sqrt (hprimes p hp))
    _ = _ := by simp; ring

theorem quadratic_gram_euler_le_exp {L : ℕ} {lam z : ℝ}
    (hlam : 0 ≤ lam) (hz : 0 < z) (hprimes : ∀ p ∈ L.primeFactors, z ≤ (p : ℝ)) :
    (∏ p ∈ L.primeFactors, (1+lam^2+2*lam/Real.sqrt (p : ℝ))) ≤
      Real.exp ((L.primeFactors.card : ℝ)*(lam^2+2*lam/Real.sqrt z)) := by
  have heq : (∏ p ∈ L.primeFactors, (1+lam^2+2*lam/Real.sqrt (p : ℝ))) =
      ∏ p ∈ L.primeFactors, (1+(lam^2+2*lam/Real.sqrt (p : ℝ))) := by
    apply Finset.prod_congr rfl
    intro p hp
    ring
  rw [heq]
  apply (Real.prod_one_add_le_exp_sum L.primeFactors
    (f := fun p : ℕ => lam^2+2*lam/Real.sqrt (p : ℝ)) (fun p => by positivity)).trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ∑ _p ∈ L.primeFactors, (lam^2+2*lam/Real.sqrt z) := by
      apply Finset.sum_le_sum
      intro p hp
      exact add_le_add le_rfl (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hz)
        (Real.sqrt_le_sqrt (hprimes p hp)))
    _ = _ := by simp; ring

end Ostmann.QuadraticCenter

end

end OAI
