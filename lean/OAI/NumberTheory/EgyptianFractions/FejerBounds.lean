import Mathlib

namespace OAI
open scoped BigOperators

namespace Problem337.GeometricKernel

/-- The basic geometric-sum bound on the closed unit disc. -/
theorem norm_geometric_sum_le (h : ℕ) (z : ℂ)
    (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    ‖∑ j ∈ Finset.range h, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hz1, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ h - 1‖ ≤ ‖z ^ h‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by
      simp only [norm_pow, norm_one]
      exact add_le_add_left (pow_le_one₀ (norm_nonneg z) hz) 1
    _ = 2 := by norm_num

/-- The nonnegative, degree-normalized squared geometric sum. -/
noncomputable def kernel (h : ℕ) (z : ℂ) : ℝ :=
  ‖∑ j ∈ Finset.range h, z ^ j‖ ^ 2 / (h : ℝ)

theorem kernel_nonneg (h : ℕ) (z : ℂ) : 0 ≤ kernel h z := by
  unfold kernel
  positivity

theorem kernel_le_degree (h : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    kernel h z ≤ h := by
  by_cases hh : h = 0
  · subst h
    simp [kernel]
  have hhR : (0 : ℝ) < h := by exact_mod_cast (Nat.pos_of_ne_zero hh)
  have hsum : ‖∑ j ∈ Finset.range h, z ^ j‖ ≤ (h : ℝ) := by
    calc
      ‖∑ j ∈ Finset.range h, z ^ j‖ ≤ ∑ j ∈ Finset.range h, ‖z ^ j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range h, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg z) hz
      _ = h := by simp
  unfold kernel
  apply (div_le_iff₀ hhR).mpr
  nlinarith [norm_nonneg (∑ j ∈ Finset.range h, z ^ j)]

/-- Pointwise decay of the normalized kernel away from the identity. -/
theorem kernel_le_four_div (h : ℕ) (hh : 0 < h) (z : ℂ)
    (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    kernel h z ≤ 4 / ((h : ℝ) * ‖z - 1‖ ^ 2) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hsum := norm_geometric_sum_le h z hz hz1
  have hsquare : ‖∑ j ∈ Finset.range h, z ^ j‖ ^ 2 ≤ (2 / ‖z - 1‖) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hsum 2
  unfold kernel
  calc
    ‖∑ j ∈ Finset.range h, z ^ j‖ ^ 2 / (h : ℝ) ≤
        (2 / ‖z - 1‖) ^ 2 / (h : ℝ) :=
      div_le_div_of_nonneg_right hsquare hhR.le
    _ = 4 / ((h : ℝ) * ‖z - 1‖ ^ 2) := by ring

theorem cyclic_geometric_sum_eq {q : ℕ} [NeZero q] (h : ℕ) (x : ZMod q) :
    (∑ j ∈ Finset.range h, ZMod.stdAddChar ((j : ZMod q) * x)) =
      ∑ j ∈ Finset.range h, (ZMod.stdAddChar x) ^ j := by
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [nsmul_eq_mul] using ZMod.stdAddChar.map_nsmul_eq_pow j x

theorem norm_cyclic_geometric_sum_le {q : ℕ} [NeZero q]
    (h : ℕ) (x : ZMod q) (hx : x ≠ 0) :
    ‖∑ j ∈ Finset.range h, ZMod.stdAddChar ((j : ZMod q) * x)‖ ≤
      2 / ‖ZMod.stdAddChar x - 1‖ := by
  rw [cyclic_geometric_sum_eq]
  apply norm_geometric_sum_le
  · simp [ZMod.stdAddChar_apply]
  · intro h
    apply hx
    apply ZMod.injective_stdAddChar
    simpa using h

end Problem337.GeometricKernel

end OAI
