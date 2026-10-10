import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightEndpoint
import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightThreshold

namespace OAI

open Erdos970

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem high_weight_mass_le_exponential :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (X L a : ℕ),
      0 < L → 2 * L ^ 2 ≤ X →
      (∀ n ∈ S, Squarefree n) → (∀ n ∈ S, n.Coprime L) →
      (∀ n ∈ S, Nat.ModEq L n a) → (∀ n ∈ S, n ≤ 2 * X) →
      ∀ u v H : ℝ, 1 < u → 1 ≤ v → 0 ≤ H →
      (∀ n ∈ S, Real.exp H < u ^ n.primeFactors.card) →
      (∑ n ∈ S, u ^ n.primeFactors.card) ≤
        ((X : ℝ) / (L : ℝ)) *
          Real.exp (Real.log (3 * u) +
            u ^ 2 * v * (Real.log (Real.log (2 * (X : ℝ))) + C) -
            (H / (2 * Real.log u) - 1) * Real.log v) := by
  obtain ⟨C, hC, hM⟩ := high_weight_mass_le_mertens
  refine ⟨C, hC, ?_⟩
  intro S X L a hL hX hS hcop hres hupper u v H hu hv hH hweight
  have hu0 : 0 < u := zero_lt_one.trans hu
  have ht := hM S X L a ⌊H / (2 * Real.log u)⌋₊ hL hX hS hcop hres hupper
    (fun n hn => large_prime_weight_card_bound hu hH (hweight n hn)) u v hu.le hv
  apply ht.trans
  calc
    _ ≤ (3 * u * (X : ℝ) / (L : ℝ)) *
        Real.exp (u ^ 2 * v * (Real.log (Real.log (2 * (X : ℝ))) + C) -
          (H / (2 * Real.log u) - 1) * Real.log v) :=
      mul_le_mul_of_nonneg_left (exp_div_pow_floor_le hv) (by positivity)
    _ = _ := by
      rw [show Real.log (3 * u) +
          u ^ 2 * v * (Real.log (Real.log (2 * (X : ℝ))) + C) -
          (H / (2 * Real.log u) - 1) * Real.log v =
        Real.log (3 * u) + (u ^ 2 * v * (Real.log (Real.log (2 * (X : ℝ))) + C) -
          (H / (2 * Real.log u) - 1) * Real.log v) by ring]
      rw [Real.exp_add, Real.exp_log (by positivity : (0 : ℝ) < 3 * u)]
      ring

end Ostmann.QuadraticCenter

end OAI
