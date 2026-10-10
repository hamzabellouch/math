import Mathlib

namespace OAI

universe u v

noncomputable section

open scoped BigOperators

namespace Problem313.NoiseKernel

variable {ι : Type u} {α : Type v} [Fintype ι] [Fintype α]

omit [Fintype α] in
/-- The subset-indexed spectral kernel factors coordinatewise. -/
theorem spectral_kernel (ρ : ℝ) (φ : ι → α → ℝ) (x y : α) :
    (∑ S : Finset ι, ρ ^ S.card * (∏ i ∈ S, φ i x) * (∏ i ∈ S, φ i y)) =
      ∏ i, (1 + ρ * φ i x * φ i y) := by
  classical
  rw [Finset.prod_one_add]
  simp only [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [Finset.prod_mul_distrib, Finset.prod_const]

/-- A spectral multiplier by `ρ ^ |S|` is the corresponding weighted
product-kernel operator. No orthogonality hypotheses are needed for this
algebraic identity. -/
theorem spectral_eq_kernel (ρ : ℝ) (φ : ι → α → ℝ) (w g : α → ℝ) (x : α) :
    (∑ S : Finset ι, ρ ^ S.card *
      (∑ y, w y * g y * (∏ i ∈ S, φ i y)) * (∏ i ∈ S, φ i x)) =
    ∑ y, w y * g y * ∏ i, (1 + ρ * φ i x * φ i y) := by
  classical
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← spectral_kernel ρ φ x y, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  ring

end Problem313.NoiseKernel

end

end OAI
