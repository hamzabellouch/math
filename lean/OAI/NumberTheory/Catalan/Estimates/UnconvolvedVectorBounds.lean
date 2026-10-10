import OAI.NumberTheory.Catalan.Determinants.TwoAdicSmoothedMinor

namespace OAI


noncomputable section

open Polynomial

namespace InternalCatalan

theorem unconvolvedP_entry_norm_le (N r u : ℕ) :
    ‖((Chebyshev.T ℤ (rowDistance N r : ℤ)).coeff u : ℚ_[2])‖ ≤
      (2 : ℝ) ^ (1 - (u : ℤ)) := by
  calc
    _ ≤ 1 / (2 : ℝ) ^ (u - 1) :=
      padic_two_norm_int_le_of_pow_dvd
        (chebyshev_T_coeff_two_pow_dvd (rowDistance N r : ℤ) u)
    _ = (2 : ℝ) ^ (-((u - 1 : ℕ) : ℤ)) := by
      simp only [zpow_neg, zpow_natCast, one_div]
    _ ≤ (2 : ℝ) ^ (1 - (u : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)

theorem unconvolvedD_entry_norm_le (N r u : ℕ) :
    ‖((Int.sign (rowOffset N r) *
      (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).coeff u : ℤ) : ℚ_[2])‖ ≤
      (2 : ℝ) ^ (-(u : ℤ)) := by
  have hdiv := dvd_mul_of_dvd_right
    (chebyshev_U_coeff_two_pow_dvd ((rowDistance N r : ℤ) - 1) u)
    (Int.sign (rowOffset N r))
  simpa only [zpow_neg, zpow_natCast, one_div] using
    padic_two_norm_int_le_of_pow_dvd hdiv

end InternalCatalan

end

end OAI
