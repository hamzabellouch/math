import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationMoment
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem block_moment_le (μ : ι → κ → ℝ) (v : κ → ℝ) (C : ι → ℝ)
    (j : ι) (hμ : ∀ i x, 0 ≤ μ i x) (hv : ∀ x, 0 < v x)
    (hcap : ∀ i x, μ i x * v x ≤ C i) (hnorm : ∑ x, μ j x = 1) :
    (∑ x, (v x)⁻¹ * ∏ i, μ i x * v x) ≤
      ∏ i ∈ Finset.univ.erase j, C i := by
  have hpoint (x : κ) : (v x)⁻¹ * (∏ i, μ i x * v x) ≤
      μ j x * ∏ i ∈ Finset.univ.erase j, C i := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => μ i x * v x) (Finset.mem_univ j)]
    have heq : (v x)⁻¹ * ((μ j x * v x) *
        ∏ i ∈ Finset.univ.erase j, μ i x * v x) =
        μ j x * ∏ i ∈ Finset.univ.erase j, μ i x * v x := by
      field_simp [(hv x).ne']
    rw [heq]
    apply mul_le_mul_of_nonneg_left _ (hμ j x)
    exact Finset.prod_le_prod₀ (fun i _ => mul_nonneg (hμ i x) (hv x).le)
      (fun i _ => hcap i x)
  calc
    (∑ x, (v x)⁻¹ * ∏ i, μ i x * v x) ≤
        ∑ x, μ j x * ∏ i ∈ Finset.univ.erase j, C i :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = ∏ i ∈ Finset.univ.erase j, C i := by rw [← Finset.sum_mul, hnorm, one_mul]

theorem block_kernel_moment_le (μ : ι → κ → ℝ) (v : κ → ℝ) (C : ι → ℝ)
    (j : ι) (hμ : ∀ i x, 0 ≤ μ i x) (hv : ∀ x, 0 < v x)
    (hcap : ∀ i x, μ i x * v x ≤ C i) (hnorm : ∑ x, μ j x = 1)
    (K : κ → ℝ) (hK : ∀ x, K x ≤ 2 * (v x)⁻¹) :
    (∑ x, K x * ∏ i, μ i x * v x) ≤
      2 * ∏ i ∈ Finset.univ.erase j, C i := by
  calc
    (∑ x, K x * ∏ i, μ i x * v x) ≤
        ∑ x, (2 * (v x)⁻¹) * ∏ i, μ i x * v x := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_right (hK x)
        (Finset.prod_nonneg (fun i _ => mul_nonneg (hμ i x) (hv x).le))
    _ = 2 * (∑ x, (v x)⁻¹ * ∏ i, μ i x * v x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ 2 * ∏ i ∈ Finset.univ.erase j, C i :=
      mul_le_mul_of_nonneg_left (block_moment_le μ v C j hμ hv hcap hnorm) (by norm_num)

end Ostmann.Arithmetic.HistoryCompensationMoment

end

end OAI
