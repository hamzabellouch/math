import Mathlib

namespace OAI

/-! Integer parameters for the lower-bound rank measure. -/
namespace Problem335.LowerParameters

noncomputable section

def s (n : ℕ) : ℕ :=
  if Nat.sqrt n % 2 = n % 2 then Nat.sqrt n else Nat.sqrt n - 1

def k (n : ℕ) : ℕ := (n - s n) / 2

def m (n : ℕ) : ℕ := (n + s n) / 2

def rho (n : ℕ) : ℝ := (k n : ℝ) / (m n : ℝ)

def lambda (n : ℕ) : ℝ := (k n : ℝ) / (n : ℝ)

def v (n : ℕ) : ℕ := k n * n ^ 2

def u (n : ℕ) : ℕ := m n * n ^ 2

theorem s_le_nat_sqrt (n : ℕ) : s n ≤ Nat.sqrt n := by
  unfold s
  split <;> omega

theorem nat_sqrt_le_s_add_one (n : ℕ) : Nat.sqrt n ≤ s n + 1 := by
  unfold s
  split <;> omega

theorem s_le_n (n : ℕ) : s n ≤ n :=
  (s_le_nat_sqrt n).trans (Nat.sqrt_le_self n)

theorem s_mod_two (n : ℕ) : s n % 2 = n % 2 := by
  by_cases hn : n = 0
  · subst n
    norm_num [s]
  have hs : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero hn)
  unfold s
  split <;> omega

theorem two_mul_k (n : ℕ) : 2 * k n = n - s n := by
  have hs := s_le_n n
  have hp := s_mod_two n
  unfold k
  omega

theorem two_mul_m (n : ℕ) : 2 * m n = n + s n := by
  have hp := s_mod_two n
  unfold m
  omega

theorem k_add_m (n : ℕ) : k n + m n = n := by
  have hs := s_le_n n
  have hk := two_mul_k n
  have hm := two_mul_m n
  omega

theorem m_eq_k_add_s (n : ℕ) : m n = k n + s n := by
  have hs := s_le_n n
  have hk := two_mul_k n
  have hm := two_mul_m n
  omega

theorem s_le_sqrt (n : ℕ) : (s n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have h : (s n : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast s_le_nat_sqrt n
  exact h.trans Real.nat_sqrt_le_real_sqrt

theorem sqrt_sub_two_lt_s (n : ℕ) : Real.sqrt (n : ℝ) - 2 < (s n : ℝ) := by
  have h₁ := Real.real_sqrt_lt_nat_sqrt_succ (a := n)
  have h₂ : (Nat.sqrt n : ℝ) ≤ (s n : ℝ) + 1 := by
    exact_mod_cast nat_sqrt_le_s_add_one n
  linarith

theorem sqrt_half_le_s {n : ℕ} (hn : 16 ≤ n) :
    Real.sqrt (n : ℝ) / 2 ≤ (s n : ℝ) := by
  have h₁ := sqrt_sub_two_lt_s n
  have h₂ : 4 ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    exact_mod_cast hn
  linarith

theorem s_pos {n : ℕ} (hn : 4 ≤ n) : 0 < s n := by
  have h₁ : 2 ≤ Nat.sqrt n := Nat.le_sqrt'.mpr hn
  have h₂ := nat_sqrt_le_s_add_one n
  omega

theorem k_pos {n : ℕ} (hn : 4 ≤ n) : 0 < k n := by
  have h₁ : Nat.sqrt n < n := Nat.sqrt_lt_self (by omega)
  have h₂ := s_le_nat_sqrt n
  have h₃ := two_mul_k n
  omega

theorem k_lt_m {n : ℕ} (hn : 4 ≤ n) : k n < m n := by
  have h₁ := m_eq_k_add_s n
  have h₂ := s_pos hn
  omega

theorem m_pos {n : ℕ} (hn : 4 ≤ n) : 0 < m n := by
  have := k_lt_m hn
  omega

theorem two_mul_k_add_s (n : ℕ) : 2 * k n + s n = n := by
  have h₁ := k_add_m n
  have h₂ := m_eq_k_add_s n
  omega

theorem s_le_quarter {n : ℕ} (hn : 16 ≤ n) : (s n : ℝ) ≤ (n : ℝ) / 4 := by
  have hs := s_le_sqrt n
  have hroot : 4 ≤ Real.sqrt (n : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    exact_mod_cast hn
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  nlinarith

theorem three_mul_n_le_eight_mul_k {n : ℕ} (hn : 16 ≤ n) :
    3 * n ≤ 8 * k n := by
  have hs := s_le_quarter hn
  have hk : 2 * (k n : ℝ) + (s n : ℝ) = (n : ℝ) := by
    exact_mod_cast two_mul_k_add_s n
  have h : 3 * (n : ℝ) ≤ 8 * (k n : ℝ) := by linarith
  exact_mod_cast h

theorem lambda_ge_three_eighths {n : ℕ} (hn : 16 ≤ n) :
    (3 : ℝ) / 8 ≤ lambda n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [lambda, le_div_iff₀ hpos]
  have h : 3 * (n : ℝ) ≤ 8 * (k n : ℝ) := by
    exact_mod_cast three_mul_n_le_eight_mul_k hn
  linarith

theorem rho_pos {n : ℕ} (hn : 4 ≤ n) : 0 < rho n := by
  unfold rho
  apply div_pos <;> exact_mod_cast (by first | exact k_pos hn | exact m_pos hn)

theorem rho_lt_one {n : ℕ} (hn : 4 ≤ n) : rho n < 1 := by
  have hm : (0 : ℝ) < m n := by exact_mod_cast m_pos hn
  rw [rho, div_lt_one hm]
  exact_mod_cast k_lt_m hn

theorem lambda_eq_half_sub {n : ℕ} (hn : 0 < n) :
    lambda n = 1 / 2 - (s n : ℝ) / (2 * (n : ℝ)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hk : 2 * (k n : ℝ) + (s n : ℝ) = (n : ℝ) := by
    exact_mod_cast two_mul_k_add_s n
  unfold lambda
  field_simp
  linarith

theorem lambda_eq_rho_div {n : ℕ} (hn : 4 ≤ n) :
    lambda n = rho n / (1 + rho n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hm : (m n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (m_pos hn))
  have hsum : (k n : ℝ) + (m n : ℝ) = (n : ℝ) := by
    exact_mod_cast k_add_m n
  unfold lambda rho
  field_simp
  nlinarith

theorem lambda_mul_n (n : ℕ) : lambda n * (n : ℝ) = (k n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    norm_num [lambda, k, s]
  · exact div_mul_cancel₀ _ (by exact_mod_cast hn)

theorem k_le_n (n : ℕ) : k n ≤ n := by
  have := k_add_m n
  omega

theorem m_le_n (n : ℕ) : m n ≤ n := by
  have := k_add_m n
  omega

theorem n_le_two_mul_m (n : ℕ) : n ≤ 2 * m n := by
  have := two_mul_m n
  omega

theorem s_is_greatest (n j : ℕ) (hj : j ≤ Nat.sqrt n)
    (hp : j % 2 = n % 2) : j ≤ s n := by
  unfold s
  split <;> omega

theorem four_mul_s_le_n {n : ℕ} (hn : 16 ≤ n) : 4 * s n ≤ n := by
  have hs := s_le_quarter hn
  have : 4 * (s n : ℝ) ≤ (n : ℝ) := by linarith
  exact_mod_cast this

theorem s_lt_k {n : ℕ} (hn : 16 ≤ n) : s n < k n := by
  have h₁ := four_mul_s_le_n hn
  have h₂ := two_mul_k_add_s n
  have h₃ := s_pos (show 4 ≤ n by omega)
  omega

theorem lambda_lt_half {n : ℕ} (hn : 4 ≤ n) : lambda n < 1 / 2 := by
  rw [lambda_eq_half_sub (show 0 < n by omega)]
  have hs : (0 : ℝ) < s n := by exact_mod_cast s_pos hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have : 0 < (s n : ℝ) / (2 * (n : ℝ)) := by positivity
  linarith

theorem one_sub_rho {n : ℕ} (hn : 4 ≤ n) :
    1 - rho n = (s n : ℝ) / (m n : ℝ) := by
  have hm : (m n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (m_pos hn))
  have h : (m n : ℝ) = (k n : ℝ) + (s n : ℝ) := by
    exact_mod_cast m_eq_k_add_s n
  unfold rho
  field_simp
  linarith

theorem v_pos {n : ℕ} (hn : 4 ≤ n) : 0 < v n := by
  unfold v
  exact Nat.mul_pos (k_pos hn) (Nat.pow_pos (by omega))

theorem u_pos {n : ℕ} (hn : 4 ≤ n) : 0 < u n := by
  unfold u
  exact Nat.mul_pos (m_pos hn) (Nat.pow_pos (by omega))

theorem v_le_cube (n : ℕ) : v n ≤ n ^ 3 := by
  unfold v
  calc k n * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right _ (k_le_n n)
       _ = n ^ 3 := by ring

theorem u_le_cube (n : ℕ) : u n ≤ n ^ 3 := by
  unfold u
  calc m n * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right _ (m_le_n n)
       _ = n ^ 3 := by ring

theorem three_mul_cube_le_eight_mul_v {n : ℕ} (hn : 16 ≤ n) :
    3 * n ^ 3 ≤ 8 * v n := by
  have h := Nat.mul_le_mul_right (n ^ 2) (three_mul_n_le_eight_mul_k hn)
  dsimp [v]
  nlinarith [h]

theorem cube_le_two_mul_u (n : ℕ) : n ^ 3 ≤ 2 * u n := by
  have h := Nat.mul_le_mul_right (n ^ 2) (n_le_two_mul_m n)
  dsimp [u]
  nlinarith [h]

end
end Problem335.LowerParameters

end OAI
