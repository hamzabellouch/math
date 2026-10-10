import OAI.LinearAlgebra.MatrixMultiplication.Numerical.ComplexCertificatesDual

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitness

private def massA (s : State) : ℝ := s.rho * s.hB + (1 - s.rho) * s.hA
private def massC (s : State) : ℝ := s.rho * s.hB + (1 - s.rho) * s.hC

private theorem massA_eq_massC (s : State) :
    massA s = massC s + (1 - s.rho) * (s.hA - s.hC) := by
  dsimp [massA, massC]
  ring

private theorem massC_eq_massA (s : State) :
    massC s = massA s + (1 - s.rho) * (s.hC - s.hA) := by
  dsimp [massA, massC]
  ring

private theorem minus_massA (m : ℕ) (s : State) (h : 1 - s.rho ^ m ≠ 0) :
    massA (minus m s) = m * massA s := by
  dsimp [massA, minus]
  field_simp
  ring

private theorem minus_massC (m : ℕ) (s : State) (h : 1 - s.rho ^ m ≠ 0) :
    massC (minus m s) = m * massC s := by
  dsimp [massC, minus]
  field_simp
  ring

private theorem minus_gap (m : ℕ) (s : State) :
    (minus m s).hC - (minus m s).hA =
      m * ((1 - s.rho) / (1 - s.rho ^ m)) * (s.hC - s.hA) := by
  dsimp [minus]
  ring

private theorem minus_gap_reverse (m : ℕ) (s : State) :
    (minus m s).hA - (minus m s).hC =
      m * ((1 - s.rho) / (1 - s.rho ^ m)) * (s.hA - s.hC) := by
  dsimp [minus]
  ring

private theorem plusA_massA (m : ℕ) (s : State)
    (h : 1 - (1 - s.rho) ^ m ≠ 0) :
    massA (plusA m s) = m * massA s := by
  dsimp [massA, plusA]
  field_simp
  ring

private theorem plusC_massC (m : ℕ) (s : State)
    (h : 1 - (1 - s.rho) ^ m ≠ 0) :
    massC (plusC m s) = m * massC s := by
  dsimp [massC, plusC]
  field_simp
  ring

private theorem log_exp_sum_pow_sub (a c : ℝ) (m : ℕ) (hm : m ≠ 0) :
    Real.log ((Real.exp a + Real.exp c) ^ m - Real.exp ((m : ℝ) * a)) =
      (m : ℝ) * a + Real.log ((1 + Real.exp (c - a)) ^ m - 1) := by
  have h : (1 + Real.exp (c - a)) ^ m - 1 ≠ 0 :=
    (sub_pos.mpr (one_lt_pow₀ (by linarith [Real.exp_pos (c - a)]) hm)).ne'
  have hfactor : Real.exp a + Real.exp c =
      Real.exp a * (1 + Real.exp (c - a)) := by
    rw [mul_add, mul_one, ← Real.exp_add, show a + (c - a) = c by ring]
  have harg : (Real.exp a + Real.exp c) ^ m - Real.exp ((m : ℝ) * a) =
      Real.exp ((m : ℝ) * a) * ((1 + Real.exp (c - a)) ^ m - 1) := by
    rw [hfactor, mul_pow, Real.exp_nat_mul a m]
    ring
  rw [harg, Real.log_mul (Real.exp_ne_zero _) h, Real.log_exp]

theorem state4_hB : state4.hB = 0 := by
  norm_num [state4, state2, initial, minus, plusA]

theorem state4_hA : state4.hA = 0 := by
  norm_num [state4, state2, initial, minus, plusA]

theorem state4_hC : state4.hC = Real.log 3 := by
  norm_num [state4, state2, initial, minus, plusA]

theorem state8_hB : state8.hB = (18 / 25 : ℝ) * Real.log 3 := by
  simp only [state8, plusC, state4_hB, state4_hC]
  norm_num [state4, state2, initial, minus, plusA]
  ring

theorem state8_hA : state8.hA = Real.log 7 := by
  simp only [state8, plusC, state4_hC, state4_hA]
  have he2 := Real.exp_nat_mul (Real.log 3) 2
  norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 3)] at he2
  norm_num [he2, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

theorem state8_hC : state8.hC = 2 * Real.log 3 := by
  simp [state8, plusC, state4_hC]

theorem state8_hidden : state8.hB = (18 / 25 : ℝ) * Real.log 3 ∧
    state8.hA = Real.log 7 ∧ state8.hC = 2 * Real.log 3 :=
  ⟨state8_hB, state8_hA, state8_hC⟩

theorem state8_gap : state8.hC - state8.hA = Real.log (9 / 7 : ℝ) := by
  rw [state8_hC, state8_hA, Real.log_div (by norm_num : (9 : ℝ) ≠ 0)
    (by norm_num : (7 : ℝ) ≠ 0)]
  have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h9]

theorem state24_gap : state24.hC - state24.hA = delta24 := by
  rw [state24, minus_gap, state8_rho, state8_gap]
  dsimp [delta24, rho24]
  norm_num
  ring

theorem state48_gap : state48.hA - state48.hC = z48 := by
  change Real.log ((Real.exp state24.hC + Real.exp state24.hA) ^ 2 -
    Real.exp (2 * state24.hC)) - 2 * state24.hC = z48
  have hlog := log_exp_sum_pow_sub state24.hC state24.hA 2 (by norm_num)
  simp only [Nat.cast_ofNat] at hlog
  rw [hlog]
  have hgap : state24.hA - state24.hC = -delta24 := by
    linarith [state24_gap]
  rw [hgap]
  dsimp [z48]
  ring

theorem state96_gap : state96.hA - state96.hC = delta96 := by
  rw [state96, minus_gap_reverse, state48_rho, state48_gap]
  norm_num [delta96, rho48, rho24, rho8]
  ring

theorem state288_gap : state288.hC - state288.hA = z288 := by
  change Real.log ((Real.exp state96.hA + Real.exp state96.hC) ^ 3 -
    Real.exp (3 * state96.hA)) - 3 * state96.hA = z288
  have hlog := log_exp_sum_pow_sub state96.hA state96.hC 3 (by norm_num)
  simp only [Nat.cast_ofNat] at hlog
  rw [hlog]
  have hgap : state96.hC - state96.hA = -delta96 := by
    linarith [state96_gap]
  rw [hgap]
  dsimp [z288]
  ring

theorem initial_max : max initial.hA initial.hC = initial.hA := by
  norm_num [initial]

theorem state2_max : max state2.hA state2.hC = state2.hA := by
  norm_num [state2, minus, initial]

theorem state4_max : max state4.hA state4.hC = state4.hC := by
  apply max_eq_right
  rw [state4_hA, state4_hC]
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le

theorem state8_max : max state8.hA state8.hC = state8.hC := by
  apply max_eq_right
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 9 / 7)
  linarith [state8_gap]

theorem state24_max : max state24.hA state24.hC = state24.hC := by
  apply max_eq_right
  linarith [state24_gap, ComplexCertificates.delta24_bounds.1]

theorem state48_max : max state48.hA state48.hC = state48.hA := by
  apply max_eq_left
  linarith [state48_gap, ComplexCertificates.z48_bounds.1]

theorem state96_max : max state96.hA state96.hC = state96.hA := by
  apply max_eq_left
  linarith [state96_gap, ComplexCertificates.delta96_bounds.1]

theorem state288_max : max state288.hA state288.hC = state288.hC := by
  apply max_eq_right
  linarith [state288_gap, ComplexCertificates.z288_bounds.1]

private theorem state8_mass : massC state8 = (9 / 8 : ℝ) * Real.log 3 := by
  dsimp [massC]
  rw [state8_rho, state8_hB, state8_hC]
  norm_num [rho8]
  ring

private theorem state24_mass : massC state24 = 3 * massC state8 := by
  apply minus_massC
  rw [state8_rho]
  exact ne_of_gt (sub_pos.mpr rho24_range.2)

private theorem state48_mass :
    massA state48 = 2 * massC state24 + (1 - rho48) * z48 := by
  rw [massA_eq_massC, state48_gap, state48_rho]
  congr 1
  apply plusC_massC
  rw [state24_rho]
  exact ne_of_gt rho48_range.1

private theorem state96_mass : massA state96 = 2 * massA state48 := by
  apply minus_massA
  rw [state48_rho]
  exact ne_of_gt (sub_pos.mpr rho96_range.2)

private theorem state288_mass :
    massC state288 = 3 * massA state96 + (1 - rho288) * z288 := by
  rw [massC_eq_massA, state288_gap, state288_rho]
  congr 1
  apply plusA_massA
  rw [state96_rho]
  exact ne_of_gt rho288_range.1

theorem state288_normalizedHidden : normalizedHidden state288 = hiddenRate := by
  rw [normalizedHidden, state288_max, state_factors]
  change massC state288 / 288 = hiddenRate
  rw [state288_mass, state96_mass, state48_mass, state24_mass, state8_mass]
  dsimp [hiddenRate]
  ring

end MatrixMultiplication.DualWitness

end

end OAI
