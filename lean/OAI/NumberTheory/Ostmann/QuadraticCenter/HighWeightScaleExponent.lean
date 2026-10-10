import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightScaleBudget

namespace OAI

namespace Ostmann.QuadraticCenter

theorem high_weight_scale_exponent_le {T u K C : ℝ} {X : ℕ}
    (hT : 2 ≤ T) (hC : 0 < C) (hu : 1 < u)
    (huupper : u ≤ T ^ ((1 : ℝ) / 100000))
    (hK : T ^ ((3 : ℝ) / 4) ≤ K) (hX : 1 ≤ X)
    (hXupper : (X : ℝ) ≤ Real.exp (T ^ 2))
    (hbudget : Real.log 3 + ((1 : ℝ) / 100000 + 1 / 4) * Real.log T +
      T ^ ((1 : ℝ) / 3) * (3 * Real.log T + C) ≤ T ^ ((3 : ℝ) / 4)) :
    Real.log (3 * u) +
      u ^ 2 * T ^ ((1 : ℝ) / 4) * (Real.log (Real.log (2 * (X : ℝ))) + C) -
      ((K / 200) / (2 * Real.log u) - 1) * Real.log (T ^ ((1 : ℝ) / 4)) ≤ -10 * K := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hu0 : 0 < u := zero_lt_one.trans hu
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlu : 0 < Real.log u := Real.log_pos hu
  have hK0 : 0 ≤ K := (Real.rpow_nonneg hT0.le _).trans hK
  have hlogu : Real.log u ≤ ((1 : ℝ) / 100000) * Real.log T := by
    have hh := Real.log_le_log hu0 huupper
    simpa only [Real.log_rpow hT0] using hh
  have hcoef : u ^ 2 * T ^ ((1 : ℝ) / 4) ≤ T ^ ((1 : ℝ) / 3) := by
    calc
      _ ≤ (T ^ ((1 : ℝ) / 100000)) ^ 2 * T ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu0.le huupper 2) (Real.rpow_nonneg hT0.le _)
      _ = T ^ (((1 : ℝ) / 100000) * 2 + 1 / 4) := by
        rw [← Real.rpow_mul_natCast hT0.le, ← Real.rpow_add hT0]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hloglog := high_weight_loglog_le hT hX hXupper
  have hterm : u ^ 2 * T ^ ((1 : ℝ) / 4) *
      (Real.log (Real.log (2 * (X : ℝ))) + C) ≤
        T ^ ((1 : ℝ) / 3) * (3 * Real.log T + C) := by
    calc
      _ ≤ u ^ 2 * T ^ ((1 : ℝ) / 4) * (3 * Real.log T + C) :=
        mul_le_mul_of_nonneg_left (add_le_add hloglog le_rfl) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hlog3u : Real.log (3 * u) ≤ Real.log 3 + ((1 : ℝ) / 100000) * Real.log T := by
    rw [Real.log_mul (by norm_num) hu0.ne']
    exact add_le_add le_rfl hlogu
  have hlogv : Real.log (T ^ ((1 : ℝ) / 4)) = ((1 : ℝ) / 4) * Real.log T :=
    Real.log_rpow hT0 _
  have hpos : Real.log (3 * u) +
      u ^ 2 * T ^ ((1 : ℝ) / 4) * (Real.log (Real.log (2 * (X : ℝ))) + C) +
      Real.log (T ^ ((1 : ℝ) / 4)) ≤ K := by
    rw [hlogv]
    linarith
  have hratio : 8000 * Real.log u ≤ Real.log (T ^ ((1 : ℝ) / 4)) := by
    rw [hlogv]
    linarith
  have hmain : 20 * K ≤ ((K / 200) / (2 * Real.log u)) *
      Real.log (T ^ ((1 : ℝ) / 4)) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log u)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hratio hK0]
  nlinarith

end Ostmann.QuadraticCenter

end OAI
