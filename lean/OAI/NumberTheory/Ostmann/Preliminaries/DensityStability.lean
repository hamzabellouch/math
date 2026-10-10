import OAI.NumberTheory.Ostmann.Preliminaries.LocalUniformity

namespace OAI

open Erdos970

namespace Ostmann.Preliminaries
open scoped BigOperators

theorem density_deviation_le_penalty {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    16 * (σ - 1 / 2) ^ 2 ≤ σ⁻¹ + (1 - σ)⁻¹ - 4 := by
  have ht : 0 < 1 - σ := by linarith
  have heq : σ⁻¹ + (1 - σ)⁻¹ - 4 = (2 * σ - 1)^2 / (σ * (1 - σ)) := by
    field_simp
    ring
  rw [heq]
  apply (le_div_iff₀ (mul_pos hσ ht)).mpr
  nlinarith [sq_nonneg ((2 * σ - 1)^2)]

theorem weighted_density_deviation_le {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (d : Decomposition) (Q : ℕ)
    (a : α → ℕ) (μ : α → ℝ) (b : β → ℕ) (ν : β → ℝ) :
    (∑ p : PrimeUpTo Q, (Real.log p.val / p.val) *
      (d.residueDensity p.val - 1 / 2) ^ 2) ≤ collisionStability d Q a μ b ν / 16 := by
  have hsum : 16 * (∑ p : PrimeUpTo Q, (Real.log p.val / p.val) *
      (d.residueDensity p.val - 1 / 2) ^ 2) ≤
      ∑ p : PrimeUpTo Q, Real.log p.val *
        (((d.residueDensity p.val)⁻¹ + (1 - d.residueDensity p.val)⁻¹ - 4) / p.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    have hp : (0 : ℝ) < p.val := by exact_mod_cast (primeUpTo_prime p).pos
    have hlog : 0 ≤ Real.log (p.val : ℝ) := Real.log_nonneg
      (by exact_mod_cast (primeUpTo_prime p).one_le)
    have h := mul_le_mul_of_nonneg_left
      (density_deviation_le_penalty (d.residueDensity_pos p.val (primeUpTo_prime p))
        (d.residueDensity_lt_one p.val (primeUpTo_prime p))) (div_nonneg hlog hp.le)
    convert h using 1 <;> ring
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  simpa only [mul_comm] using hsum.trans (weighted_density_penalty_le d Q a μ b ν)

end Ostmann.Preliminaries

end OAI
