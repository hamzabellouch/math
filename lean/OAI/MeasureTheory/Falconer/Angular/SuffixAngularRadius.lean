import OAI.MeasureTheory.Falconer.Angular.AngularWidths

namespace OAI

namespace PlanarFalconer

theorem dyadic_ratio_le_radius {a p l N : ℕ} {sig : ℝ}
    (hsig : 0 ≤ sig) (hl : a+l ≤ p) :
    (2:ℝ)^a/(2:ℝ)^p ≤ sourceAngularRadius N sig l := by
  have hpow : (2:ℝ)^a*(2:ℝ)^l ≤ (2:ℝ)^p := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) hl
  have hsub : (2:ℝ)^a/(2:ℝ)^p ≤ 1/(2:ℝ)^l := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simpa only [one_mul] using hpow
  have hR : 1 ≤ ((2:ℝ)^N)^(50*sig) :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity)
  apply le_min
  · exact (div_le_one (by positivity)).mpr
      (pow_le_pow_right₀ (by norm_num) (by omega))
  · exact hsub.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 1/(2:ℝ)^l))

theorem suffix_direction_scale {a p u : ℕ} (hs : a+u ≤ 2*p) (hpu : p ≤ u) :
    (2:ℝ)^a/(2:ℝ)^p ≤ 1/(2:ℝ)^(u-p) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul,← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

end PlanarFalconer

end OAI
