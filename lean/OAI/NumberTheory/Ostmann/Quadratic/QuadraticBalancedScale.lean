import OAI.NumberTheory.Ostmann.Quadratic.QuadraticBalancedKernel

namespace OAI

/-! # The balanced kernel gives Heath-Brown's improved long-row scale -/

namespace Ostmann

theorem quadratic_balanced_power_identity {M N Y ξ : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hY : 0 ≤ Y) :
    Real.sqrt M * (16 * N ^ 2 * Y / M) ^ (ξ - 1 / 2) =
      16 ^ (ξ - 1 / 2) * Y ^ (ξ - 1 / 2) * (M ^ (1 - ξ) * N ^ (2 * ξ - 1)) := by
  have hm : M ^ (1 - ξ) = M ^ (1 / 2 : ℝ) / M ^ (ξ - 1 / 2) := by
    rw [← Real.rpow_sub hM]
    congr 1
    ring
  have hn : (N ^ 2) ^ (ξ - 1 / 2) = N ^ (2 * ξ - 1) := by
    rw [← Real.rpow_natCast N 2, ← Real.rpow_mul hN.le]
    congr 1
    ring
  rw [Real.div_rpow (by positivity) hM.le, Real.mul_rpow (by positivity) hY,
    Real.mul_rpow (by norm_num) (by positivity), hn, Real.sqrt_eq_rpow, hm]
  ring

theorem quadratic_balanced_scale {ξ η : ℝ} (hξ : 1 / 2 ≤ ξ) (hξ' : ξ ≤ 2)
    (hη : 0 ≤ η) {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hsep : 4 * (N : ℝ) * (((M : ℝ) * N) ^ η) ≤ M) :
    quadraticDescentScale ξ M N (quadraticBalancedKernel η M N) ≤
      300 * (((M : ℝ) * N) ^ η) ^ 2 *
        ((M : ℝ) + (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)) := by
  let K := quadraticBalancedKernel η M N
  let Y := ((M : ℝ) * N) ^ η
  let S := (M : ℝ) ^ (1 - ξ) * (N : ℝ) ^ (2 * ξ - 1)
  have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hY : 1 ≤ Y := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hM₁ hN₁) hη
  obtain ⟨hK, _, hKu, hKl⟩ := quadratic_balanced_kernel_bounds hη hM hN hsep
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hNM : (N : ℝ) ≤ M := by
    have hh := mul_le_mul_of_nonneg_left hY hNR.le
    change 4 * (N : ℝ) * Y ≤ M at hsep
    nlinarith
  have hSm : 0 ≤ S := by dsimp [S]; positivity
  have hYm : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hsqrtM : Real.sqrt M ≤ M := Real.sqrt_le_self_iff.mpr (Or.inr hM₁)
  have htail : Real.sqrt M * N / Real.sqrt K ≤ M := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hKR)).mpr
    have hsq : (Real.sqrt M * (N : ℝ)) ^ 2 ≤ ((M : ℝ) * Real.sqrt K) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hMR.le, Real.sq_sqrt hKR.le]
      have hyN := mul_le_mul_of_nonneg_left hY (sq_nonneg (N : ℝ))
      change 8 * (N : ℝ) ^ 2 * Y ≤ (M : ℝ) * K at hKl
      nlinarith
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  have hkernel : Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) ≤
      4 * M + 256 * Y ^ 2 * S := by
    by_cases hq : 8 * (N : ℝ) ^ 2 * Y / M ≤ 1
    · have hK₂ : (K : ℝ) ≤ 2 := by
        change (K : ℝ) ≤ 8 * (N : ℝ) ^ 2 * Y / M + 1 at hKu
        linarith
      have hp : (K : ℝ) ^ (ξ - 1 / 2) ≤ 4 := by
        calc
          _ ≤ (2 : ℝ) ^ (ξ - 1 / 2) := Real.rpow_le_rpow hKR.le hK₂ (by linarith)
          _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 4 := by norm_num
      have hh := mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg (M : ℝ))
      nlinarith
    · have hKq : (K : ℝ) ≤ 16 * (N : ℝ) ^ 2 * Y / M := by
        change (K : ℝ) ≤ 8 * (N : ℝ) ^ 2 * Y / M + 1 at hKu
        rw [show 16 * (N : ℝ) ^ 2 * Y / M = 2 * (8 * (N : ℝ) ^ 2 * Y / M) by ring]
        linarith
      have hp := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hKR.le hKq (by linarith : 0 ≤ ξ - 1 / 2))
        (Real.sqrt_nonneg (M : ℝ))
      rw [quadratic_balanced_power_identity hMR hNR (by positivity)] at hp
      have hc : (16 : ℝ) ^ (ξ - 1 / 2) ≤ 256 := by
        calc
          _ ≤ (16 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 256 := by norm_num
      have hy : Y ^ (ξ - 1 / 2) ≤ Y ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hY (by linarith)
      rw [Real.rpow_two] at hy
      have hh : (16 : ℝ) ^ (ξ - 1 / 2) * Y ^ (ξ - 1 / 2) * S ≤ 256 * Y ^ 2 * S := by
        gcongr
      change Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) ≤ _ at hp
      exact hp.trans (hh.trans (le_add_of_nonneg_left (by positivity)))
  change (M : ℝ) + N + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2) +
    Real.sqrt M * N / Real.sqrt K ≤ 300 * Y ^ 2 * ((M : ℝ) + S)
  have hmY := mul_le_mul_of_nonneg_right hYm hMR.le
  have hsY : 0 ≤ Y ^ 2 * S := mul_nonneg (sq_nonneg Y) hSm
  nlinarith

end Ostmann

end OAI
