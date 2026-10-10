import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRoughPowerGrowth

namespace OAI

/-! # The actual rounded kernel cutoff in the long-row range -/

namespace Ostmann

noncomputable def quadraticBalancedKernel (η : ℝ) (M N : ℕ) : ℕ :=
  ⌈8 * (N : ℝ) ^ 2 * (((M : ℝ) * N) ^ η) / M⌉₊

theorem quadratic_balanced_kernel_bounds {η : ℝ} (hη : 0 ≤ η)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hsep : 4 * (N : ℝ) * (((M : ℝ) * N) ^ η) ≤ M) :
    0 < quadraticBalancedKernel η M N ∧ quadraticBalancedKernel η M N < M ∧
      (quadraticBalancedKernel η M N : ℝ) ≤
        8 * (N : ℝ) ^ 2 * (((M : ℝ) * N) ^ η) / M + 1 ∧
      8 * (N : ℝ) ^ 2 * (((M : ℝ) * N) ^ η) ≤
        (M : ℝ) * quadraticBalancedKernel η M N := by
  let Y := ((M : ℝ) * N) ^ η
  let q := 8 * (N : ℝ) ^ 2 * Y / M
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hY : 1 ≤ Y := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) hNR) hη
  have hq : 0 < q := by dsimp [q]; positivity
  have hM₄ : (4 : ℝ) ≤ M := by
    have : 1 ≤ (N : ℝ) * Y := one_le_mul_of_one_le_of_one_le hNR hY
    change 4 * (N : ℝ) * Y ≤ M at hsep
    nlinarith
  have hqM : q ≤ (M : ℝ) / 2 := by
    apply (div_le_iff₀ hMR).mpr
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4 * N * Y) hsep 2
    have hYsq : Y ≤ Y ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hYsq (sq_nonneg (N : ℝ))
    nlinarith
  have hlo : q ≤ (quadraticBalancedKernel η M N : ℝ) := Nat.le_ceil _
  have hhi : (quadraticBalancedKernel η M N : ℝ) < q + 1 := Nat.ceil_lt_add_one hq.le
  have hK : (0 : ℝ) < quadraticBalancedKernel η M N := hq.trans_le hlo
  have hKM : (quadraticBalancedKernel η M N : ℝ) < M := by linarith
  refine ⟨by exact_mod_cast hK, by exact_mod_cast hKM, hhi.le, ?_⟩
  have hh := (div_le_iff₀ hMR).mp hlo
  simpa only [mul_comm] using hh

theorem quadratic_balanced_kernel_cutoff {η : ℝ} (hη : 0 ≤ η)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hsep : 4 * (N : ℝ) * (((M : ℝ) * N) ^ η) ≤ M) :
    2 * (2 * (N : ℝ)) ^ 2 * (((M : ℝ) * N) ^ η) ≤
      (M : ℝ) * ((quadraticBalancedKernel η M N : ℝ) + 1) := by
  have hh := (quadratic_balanced_kernel_bounds hη hM hN hsep).2.2.2
  nlinarith [Nat.cast_nonneg (α := ℝ) M]

end Ostmann

end OAI
