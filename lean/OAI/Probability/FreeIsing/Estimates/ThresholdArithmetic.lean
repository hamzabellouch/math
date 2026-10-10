import Mathlib

namespace OAI

noncomputable section

namespace Problem367

lemma branching_pos {d : ℕ} (hd : 3 ≤ d) : 0 < (d : ℝ) - 1 := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma threshold_sqrt_pos {d : ℕ} (hd : 3 ≤ d) :
    0 < Real.sqrt ((d : ℝ) - 1) :=
  Real.sqrt_pos.2 (branching_pos hd)

lemma threshold_iff_branching_sq {d : ℕ} {theta : ℝ}
    (hd : 3 ≤ d) (htheta : 0 ≤ theta) :
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
      ((d : ℝ) - 1) * theta ^ 2 ≤ 1 := by
  have hb := (branching_pos hd).le
  have hs := threshold_sqrt_pos hd
  calc
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
        theta * Real.sqrt ((d : ℝ) - 1) ≤ 1 := le_div_iff₀ hs
    _ ↔ (theta * Real.sqrt ((d : ℝ) - 1)) ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg htheta hs.le) (by norm_num)).symm
    _ ↔ ((d : ℝ) - 1) * theta ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt hb, one_pow, mul_comm]

lemma threshold_lt_iff_branching_sq_lt {d : ℕ} {theta : ℝ}
    (hd : 3 ≤ d) (htheta : 0 ≤ theta) :
    theta < 1 / Real.sqrt ((d : ℝ) - 1) ↔
      ((d : ℝ) - 1) * theta ^ 2 < 1 := by
  have hb := (branching_pos hd).le
  have hs := threshold_sqrt_pos hd
  calc
    theta < 1 / Real.sqrt ((d : ℝ) - 1) ↔
        theta * Real.sqrt ((d : ℝ) - 1) < 1 := lt_div_iff₀ hs
    _ ↔ (theta * Real.sqrt ((d : ℝ) - 1)) ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (mul_nonneg htheta hs.le) (by norm_num)).symm
    _ ↔ ((d : ℝ) - 1) * theta ^ 2 < 1 := by
      rw [mul_pow, Real.sq_sqrt hb, one_pow, mul_comm]

lemma tanh_nonneg_of_beta_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    0 ≤ Real.tanh beta := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta) (Real.cosh_pos beta).le

lemma tanh_mem_Ico_of_beta_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) :
    Real.tanh beta ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨tanh_nonneg_of_beta_nonneg hbeta, Real.tanh_lt_one beta⟩

lemma tanh_threshold_iff_branching_sq {d : ℕ} {beta : ℝ}
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta) :
    Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1) ↔
      ((d : ℝ) - 1) * Real.tanh beta ^ 2 ≤ 1 :=
  threshold_iff_branching_sq hd (tanh_nonneg_of_beta_nonneg hbeta)

end Problem367

end

end OAI
