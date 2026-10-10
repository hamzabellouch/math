import OAI.Algebra.DepthFive.LowerParameters

namespace OAI

/-! Rounded analytic parameters used by the lower-bound rank measure. -/
noncomputable section
namespace Problem335.LowerParameters

def a0 (n : ℕ) : ℝ := (v n : ℝ) / (Real.sqrt (n : ℝ) - 1)
def a (n : ℕ) : ℕ := ⌈a0 n⌉₊
def alpha (n : ℕ) : ℝ := (a n : ℝ) / ((a n : ℝ) + (v n : ℝ))
def b0 (n : ℕ) : ℝ := (u n : ℝ) * (alpha n) ^ (rho n) / (1 - (alpha n) ^ (rho n))
def b (n : ℕ) : ℕ := ⌈b0 n⌉₊
def beta (n : ℕ) : ℝ := (b n : ℝ) / ((b n : ℝ) + (u n : ℝ))
def q (n : ℕ) : ℝ := (alpha n) ^ ((1 + rho n) / 2)

theorem sqrt_ge_two {n : ℕ} (hn : 4 ≤ n) : 2 ≤ Real.sqrt (n : ℝ) := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  exact_mod_cast hn

theorem a0_pos {n : ℕ} (hn : 4 ≤ n) : 0 < a0 n := by
  unfold a0
  apply div_pos
  · exact_mod_cast v_pos hn
  · have := sqrt_ge_two hn
    linarith

theorem a_pos {n : ℕ} (hn : 4 ≤ n) : 0 < a n := by
  exact Nat.ceil_pos.mpr (a0_pos hn)

theorem a0_le_a (n : ℕ) : a0 n ≤ (a n : ℝ) := Nat.le_ceil _

theorem a_lt_a0_add_one {n : ℕ} (hn : 4 ≤ n) : (a n : ℝ) < a0 n + 1 :=
  Nat.ceil_lt_add_one (a0_pos hn).le

theorem alpha_pos {n : ℕ} (hn : 4 ≤ n) : 0 < alpha n := by
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos hn
  unfold alpha
  positivity

theorem alpha_lt_one {n : ℕ} (hn : 4 ≤ n) : alpha n < 1 := by
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos hn
  unfold alpha
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem inv_sqrt_le_alpha {n : ℕ} (hn : 4 ≤ n) :
    (Real.sqrt (n : ℝ))⁻¹ ≤ alpha n := by
  have hr := sqrt_ge_two hn
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos hn
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos hn
  have hround := a0_le_a n
  have hmul : (v n : ℝ) ≤ (a n : ℝ) * (Real.sqrt (n : ℝ) - 1) :=
    (div_le_iff₀ (by linarith)).mp hround
  rw [inv_eq_one_div, alpha]
  apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
  nlinarith

theorem inv_alpha_le_sqrt {n : ℕ} (hn : 4 ≤ n) :
    (alpha n)⁻¹ ≤ Real.sqrt (n : ℝ) := by
  have ha := alpha_pos hn
  have hs := sqrt_ge_two hn
  have h := inv_sqrt_le_alpha hn
  calc
    (alpha n)⁻¹ ≤ ((Real.sqrt (n : ℝ))⁻¹)⁻¹ :=
      (inv_le_inv₀ ha (inv_pos.mpr (by linarith))).mpr h
    _ = _ := inv_inv _

theorem k_mul_n_le_a0 {n : ℕ} (hn : 4 ≤ n) :
    (k n : ℝ) * (n : ℝ) ≤ a0 n := by
  have hr := sqrt_ge_two hn
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hbound : Real.sqrt (n : ℝ) - 1 ≤ (n : ℝ) := by nlinarith
  unfold a0
  apply (le_div_iff₀ (by linarith)).mpr
  have h := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ (k n : ℝ) * (n : ℝ) by positivity)
  simpa [v, Nat.cast_mul, Nat.cast_pow, pow_two, mul_assoc] using h

theorem k_mul_n_le_a {n : ℕ} (hn : 4 ≤ n) : k n * n ≤ a n := by
  have h := (k_mul_n_le_a0 hn).trans (a0_le_a n)
  exact_mod_cast h

theorem k_le_a {n : ℕ} (hn : 4 ≤ n) : k n ≤ a n := by
  exact (Nat.le_mul_of_pos_right _ (by omega)).trans (k_mul_n_le_a hn)

theorem four_mul_n_le_a {n : ℕ} (hn : 16 ≤ n) : 4 * n ≤ a n := by
  have hk := three_mul_n_le_eight_mul_k hn
  have hka := k_mul_n_le_a (show 4 ≤ n by omega)
  have hk4 : 4 ≤ k n := by omega
  exact (Nat.mul_le_mul_right n hk4).trans hka

theorem alpha_rpow_rho_pos {n : ℕ} (hn : 4 ≤ n) :
    0 < (alpha n) ^ (rho n) := Real.rpow_pos_of_pos (alpha_pos hn) _

theorem alpha_rpow_rho_lt_one {n : ℕ} (hn : 4 ≤ n) :
    (alpha n) ^ (rho n) < 1 :=
  Real.rpow_lt_one (alpha_pos hn).le (alpha_lt_one hn) (rho_pos hn)

theorem alpha_le_alpha_rpow_rho {n : ℕ} (hn : 4 ≤ n) :
    alpha n ≤ (alpha n) ^ (rho n) :=
  Real.self_le_rpow_of_le_one (alpha_pos hn).le (alpha_lt_one hn).le (rho_lt_one hn).le

theorem b0_pos {n : ℕ} (hn : 4 ≤ n) : 0 < b0 n := by
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos hn
  have hp := alpha_rpow_rho_pos hn
  have hp1 := alpha_rpow_rho_lt_one hn
  unfold b0
  positivity

theorem b_pos {n : ℕ} (hn : 4 ≤ n) : 0 < b n :=
  Nat.ceil_pos.mpr (b0_pos hn)

theorem b0_le_b (n : ℕ) : b0 n ≤ (b n : ℝ) := Nat.le_ceil _

theorem b_lt_b0_add_one {n : ℕ} (hn : 4 ≤ n) : (b n : ℝ) < b0 n + 1 :=
  Nat.ceil_lt_add_one (b0_pos hn).le

theorem beta_pos {n : ℕ} (hn : 4 ≤ n) : 0 < beta n := by
  have hb : (0 : ℝ) < b n := by exact_mod_cast b_pos hn
  unfold beta
  positivity

theorem beta_lt_one {n : ℕ} (hn : 4 ≤ n) : beta n < 1 := by
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos hn
  unfold beta
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem alpha_rpow_rho_le_beta {n : ℕ} (hn : 4 ≤ n) :
    (alpha n) ^ (rho n) ≤ beta n := by
  have hu : (0 : ℝ) < u n := by exact_mod_cast u_pos hn
  have hp := alpha_rpow_rho_lt_one hn
  have hround := b0_le_b n
  have hmul : (u n : ℝ) * (alpha n) ^ (rho n) ≤
      (b n : ℝ) * (1 - (alpha n) ^ (rho n)) :=
    (div_le_iff₀ (by linarith)).mp hround
  rw [beta]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

theorem a_le_b0 {n : ℕ} (hn : 4 ≤ n) : (a n : ℝ) ≤ b0 n := by
  have hap := alpha_pos hn
  have ha : (0 : ℝ) < a n := by exact_mod_cast a_pos hn
  have hv : (0 : ℝ) < v n := by exact_mod_cast v_pos hn
  have hu : (v n : ℝ) ≤ u n := by
    have hkm : k n ≤ m n := (k_lt_m hn).le
    exact_mod_cast Nat.mul_le_mul_right (n ^ 2) hkm
  have hp := alpha_rpow_rho_pos hn
  have hp1 := alpha_rpow_rho_lt_one hn
  have hal := alpha_le_alpha_rpow_rho hn
  have heq : (a n : ℝ) * (1 - alpha n) = (v n : ℝ) * alpha n := by
    unfold alpha
    field_simp
    ring
  unfold b0
  apply (le_div_iff₀ (by linarith)).mpr
  calc
    (a n : ℝ) * (1 - (alpha n) ^ (rho n)) ≤ (a n : ℝ) * (1 - alpha n) := by
      gcongr
    _ = (v n : ℝ) * alpha n := heq
    _ ≤ (u n : ℝ) * (alpha n) ^ (rho n) :=
      mul_le_mul hu hal hap.le (by positivity)

theorem a_le_b {n : ℕ} (hn : 4 ≤ n) : a n ≤ b n := by
  exact_mod_cast (a_le_b0 hn).trans (b0_le_b n)

theorem four_mul_n_le_b {n : ℕ} (hn : 16 ≤ n) : 4 * n ≤ b n :=
  (four_mul_n_le_a hn).trans (a_le_b (by omega))

theorem q_pos {n : ℕ} (hn : 4 ≤ n) : 0 < q n :=
  Real.rpow_pos_of_pos (alpha_pos hn) _

theorem q_lt_one {n : ℕ} (hn : 4 ≤ n) : q n < 1 := by
  have hr := rho_pos hn
  exact Real.rpow_lt_one (alpha_pos hn).le (alpha_lt_one hn) (by linarith)

theorem alpha_le_q {n : ℕ} (hn : 4 ≤ n) : alpha n ≤ q n := by
  have hr := rho_lt_one hn
  exact Real.self_le_rpow_of_le_one (alpha_pos hn).le (alpha_lt_one hn).le (by linarith)

theorem q_le_alpha_rpow_rho {n : ℕ} (hn : 4 ≤ n) :
    q n ≤ (alpha n) ^ (rho n) := by
  have hr := rho_lt_one hn
  exact Real.rpow_le_rpow_of_exponent_ge (alpha_pos hn) (alpha_lt_one hn).le (by linarith)

theorem q_le_beta {n : ℕ} (hn : 4 ≤ n) : q n ≤ beta n :=
  (q_le_alpha_rpow_rho hn).trans (alpha_rpow_rho_le_beta hn)

theorem inv_sqrt_le_q {n : ℕ} (hn : 4 ≤ n) : (Real.sqrt (n : ℝ))⁻¹ ≤ q n :=
  (inv_sqrt_le_alpha hn).trans (alpha_le_q hn)

end Problem335.LowerParameters

end

end OAI
