import Mathlib

namespace OAI

universe u v

noncomputable section

namespace Problem313

open scoped BigOperators

/-- Removing a diagonal noise multiplier costs at most `rho ^ (-2*k)`
in squared coefficient norm on coefficients supported in degrees at most `k`. -/
theorem inverse_noise_energy_le {ι : Type u} [Fintype ι]
    (degree : ι → ℕ) (c : ι → ℝ) (rho k : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hdegree : ∀ i, c i ≠ 0 → (degree i : ℝ) ≤ k) :
    (∑ i, (rho ^ (-(degree i : ℝ)) * c i) ^ 2) ≤
      rho ^ (-2 * k) * ∑ i, (c i) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hc : c i = 0
  · simp [hc]
  have hexp : -2 * k ≤ -(degree i : ℝ) * 2 := by
    linarith [hdegree i hc]
  have hrpow := Real.rpow_le_rpow_of_exponent_ge hrho hrho1 hexp
  have hsq : (rho ^ (-(degree i : ℝ))) ^ 2 =
      rho ^ (-(degree i : ℝ) * 2) := by
    rw [Real.rpow_mul hrho.le, Real.rpow_two]
  rw [mul_pow, hsq]
  exact mul_le_mul_of_nonneg_right hrpow (sq_nonneg (c i))

/-- Spectral inversion turns a diagonal-noise `L² → L⁴` estimate into an
`L⁴` estimate for a low-degree expansion.  This version is independent of
any particular construction of the orthonormal basis. -/
theorem lowDegree_fourth_of_noise
    {ι : Type u} {X : Type v} [Fintype ι] [Fintype X]
    (degree : ι → ℕ) (basis : ι → X → ℝ) (weight : X → ℝ)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : ι → ℝ,
      (∑ x, weight x * (∑ i, rho ^ (degree i : ℝ) * a i * basis i x) ^ 4) ≤
        (∑ i, (a i) ^ 2) ^ 2)
    (c : ι → ℝ) (hdegree : ∀ i, c i ≠ 0 → (degree i : ℝ) ≤ k) :
    (∑ x, weight x * (∑ i, c i * basis i x) ^ 4) ≤
      rho ^ (-4 * k) * (∑ i, (c i) ^ 2) ^ 2 := by
  let a : ι → ℝ := fun i => rho ^ (-(degree i : ℝ)) * c i
  have hinv (i : ι) : rho ^ (degree i : ℝ) * a i = c i := by
    dsimp [a]
    rw [← mul_assoc, ← Real.rpow_add hrho]
    simp
  have hnoise' :
      (∑ x, weight x * (∑ i, c i * basis i x) ^ 4) ≤
        (∑ i, (a i) ^ 2) ^ 2 := by
    simpa only [hinv] using hnoise a
  have henergy : (∑ i, (a i) ^ 2) ≤
      rho ^ (-2 * k) * ∑ i, (c i) ^ 2 :=
    inverse_noise_energy_le degree c rho k hrho hrho1 hdegree
  have hnonneg : 0 ≤ ∑ i, (a i) ^ 2 := by positivity
  have hsq : (∑ i, (a i) ^ 2) ^ 2 ≤
      (rho ^ (-2 * k) * ∑ i, (c i) ^ 2) ^ 2 := by
    exact pow_le_pow_left₀ hnonneg henergy 2
  have hscale : (rho ^ (-2 * k) * ∑ i, (c i) ^ 2) ^ 2 =
      rho ^ (-4 * k) * (∑ i, (c i) ^ 2) ^ 2 := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_two, ← Real.rpow_mul hrho.le]
    congr 1
    ring
  exact hnoise'.trans (hsq.trans_eq hscale)

end Problem313

end

end OAI
