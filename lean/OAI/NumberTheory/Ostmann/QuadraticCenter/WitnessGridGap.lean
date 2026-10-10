import OAI.NumberTheory.Ostmann.QuadraticCenter.OffWitnessFamily

namespace OAI

/-! # The grid error is smaller than the small-kernel witness gap -/

namespace Ostmann

theorem witness_grid_gap (T : ℝ) (K : ℕ) (hT : 1 ≤ T) (hK : 1 ≤ K)
    (hKT : (K : ℝ) ≤ T) :
    Real.exp (-(K : ℝ)) + Real.exp (-128 * T) ≤ Real.exp (-9 * K / 10) := by
  have hten : (10 : ℝ) ≤ Real.exp (127 * T) := by
    linarith [Real.add_one_le_exp (127 * T)]
  have hinv : Real.exp (-127 * T) ≤ (1 / 10 : ℝ) := by
    rw [show -127 * T = -(127 * T) by ring, Real.exp_neg]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 10) hten
  have hsmall : Real.exp (-128 * T) ≤ (1 / 10 : ℝ) * Real.exp (-(K : ℝ)) := by
    calc
      _ ≤ Real.exp (-127 * T) * Real.exp (-(K : ℝ)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right hinv (Real.exp_nonneg _)
  have hkR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have he : (1 + 1 / 10 : ℝ) ≤ Real.exp ((K : ℝ) / 10) := by
    linarith [Real.add_one_le_exp ((K : ℝ) / 10)]
  calc
    _ ≤ (1 + 1 / 10 : ℝ) * Real.exp (-(K : ℝ)) := by linarith
    _ ≤ Real.exp ((K : ℝ) / 10) * Real.exp (-(K : ℝ)) :=
      mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem small_witness_failure_survives_grid (T : ℝ) (K d : ℕ) (x y : ℂ)
    (hT : 1 ≤ T) (hK : 1 ≤ K) (hKT : (K : ℝ) ≤ T)
    (hx : ‖x‖ ≤ Real.exp (-(K : ℝ)) * (Real.sqrt 2) ^ d)
    (hxy : ‖x - y‖ ≤ Real.exp (-128 * T)) :
    ‖y‖ ≤ Real.exp (-9 * K / 10) * (Real.sqrt 2) ^ d := by
  have hroot : (1 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hp : (1 : ℝ) ≤ (Real.sqrt 2) ^ d := one_le_pow₀ hroot
  have hh : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    have he : y = x - (x - y) := by ring
    calc
      ‖y‖ = ‖x - (x - y)‖ := congrArg norm he
      _ ≤ _ := norm_sub_le _ _
  calc
    _ ≤ Real.exp (-(K : ℝ)) * (Real.sqrt 2) ^ d + Real.exp (-128 * T) :=
      hh.trans (add_le_add hx hxy)
    _ ≤ (Real.exp (-(K : ℝ)) + Real.exp (-128 * T)) * (Real.sqrt 2) ^ d := by
      rw [add_mul]
      exact add_le_add_right
        (le_mul_of_one_le_right (Real.exp_nonneg _) hp) _
    _ ≤ _ := mul_le_mul_of_nonneg_right (witness_grid_gap T K hT hK hKT) (by positivity)

end Ostmann

end OAI
