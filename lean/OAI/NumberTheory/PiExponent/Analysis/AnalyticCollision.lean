import Mathlib

namespace OAI

open scoped BigOperators
open Complex Finset

namespace PiExponent.AnalyticCollision

noncomputable def exponentialMonomial (b h : ℂ) (d : ℕ) (z : ℂ) : ℂ :=
  b * Complex.exp (h * z) * z ^ d

theorem differentiable_exponentialMonomial (b h : ℂ) (d : ℕ) :
    Differentiable ℂ (exponentialMonomial b h d) := by
  exact ((Complex.differentiable_exp.comp (differentiable_id.const_mul h)).const_mul b).mul
    (differentiable_id.pow d)

theorem norm_exponentialMonomial_le (b h : ℂ) (d : ℕ) {z : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖exponentialMonomial b h d z‖ ≤ ‖b‖ * Real.exp (‖h‖ * R) * R ^ d := by
  unfold exponentialMonomial
  simp only [norm_mul, norm_pow]
  apply mul_le_mul_of_nonneg
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg b)
    exact (Complex.norm_exp_le_exp_norm _).trans
      (Real.exp_le_exp.mpr (by simpa only [norm_mul] using mul_le_mul_of_nonneg_left hz (norm_nonneg h)))
  · exact pow_le_pow_left₀ (norm_nonneg z) hz d
  · positivity
  · exact pow_nonneg hR d

noncomputable def normalizedTaylorCoeff (f : ℂ → ℂ) (R : ℝ) (d : ℕ) : ℂ :=
  cauchyPowerSeries f 0 R d (fun _ => (R : ℂ))

theorem norm_normalizedTaylorCoeff_le {f : ℂ → ℂ} {R D : ℝ} (hR : 0 < R)
    (hD : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ D) (d : ℕ) :
    ‖normalizedTaylorCoeff f R d‖ ≤ D := by
  unfold normalizedTaylorCoeff
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ R * (R⁻¹ * D) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
      intro z hz
      have hzR : ‖z‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR, norm_inv, hzR, div_self (ne_of_gt hR),
        one_pow, one_mul]
      exact mul_le_mul_of_nonneg_left (hD z hz) (inv_nonneg.mpr hR.le)
    _ = D := by field_simp

theorem hasSum_normalizedTaylorCoeff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : NNReal} (hR : 0 < R) (z : ℂ) :
    HasSum (fun d => normalizedTaylorCoeff f R d * (z / (R : ℂ)) ^ d) (f z) := by
  convert! (hf.hasFPowerSeriesOnBall 0 hR).hasSum (y := z) (by simp) using 1
  · funext d
    simp only [normalizedTaylorCoeff, cauchyPowerSeries,
      ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const, smul_eq_mul]
    have hr : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
    rw [div_pow]
    field_simp
  · simp

theorem coefficient_det_eq_zero_of_collision {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : κ → ℕ → ι → ℂ) (group : ι → κ) (degree : ι → ℕ)
    {i j : ι} (hij : i ≠ j) (hg : group i = group j) (hd : degree i = degree j) :
    Matrix.det (fun r c => coefficient (group r) (degree r) c) = 0 := by
  apply Matrix.det_zero_of_row_eq hij
  simp only [hg, hd]

theorem norm_det_le_factorial_mul_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {D : ℝ} (hD : 0 ≤ D) (hA : ∀ i j, ‖A i j‖ ≤ D) :
    ‖A.det‖ ≤ (Fintype.card ι).factorial * D ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖σ.sign • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, ‖A (σ i) i‖ := by
      apply Finset.sum_congr rfl
      intro σ _
      rcases Int.units_eq_one_or σ.sign with hs | hs <;> simp [hs, norm_prod]
    _ ≤ ∑ _σ : Equiv.Perm ι, D ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro σ _
      calc
        _ ≤ ∏ _index : ι, |D| := Finset.prod_le_prod₀
          (fun index _ => norm_nonneg _) (fun index _ => (hA (σ index) index).trans (le_abs_self D))
        _ = D ^ Fintype.card ι := by simp [abs_of_nonneg hD]
    _ = _ := by simp [Fintype.card_perm]

noncomputable def rowTest (ell : ℕ) (f : ℂ → ℂ) : ℂ :=
  cauchyPowerSeries f 0 (1 / 2) ell (fun _ => 1)

theorem norm_rowTest_le {f : ℂ → ℂ} {D : ℝ}
    (hD : ∀ t ∈ Metric.sphere (0 : ℂ) (1 / 2), ‖f t‖ ≤ D) (ell : ℕ) :
    ‖rowTest ell f‖ ≤ (2 : ℝ) ^ ell * D := by
  unfold rowTest
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ (1 / 2 : ℝ) * (2 ^ ell * (2 * D)) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by norm_num)
      intro z hz
      have hzR : ‖z‖ = (1 / 2 : ℝ) := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, norm_one, norm_inv, hzR]
      norm_num only [one_div, inv_div, div_one]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hD z hz) (by norm_num))
        (by positivity)
    _ = _ := by ring

theorem norm_shifted_log_div_le_half {center t : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ht : ‖t‖ ≤ 1 / 2) :
    ‖(center + Complex.log (1 + t)) / (R : ℂ)‖ ≤ 1 / 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  apply (div_le_iff₀ hR).mpr
  have hlog := Complex.norm_log_one_add_half_le_self ht
  have htri := norm_add_le center (Complex.log (1 + t))
  nlinarith

theorem norm_rowTest_shifted_power_le {center : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ell d : ℕ) :
    ‖rowTest ell (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)‖ ≤
      (2 : ℝ) ^ ell * (1 / 2 : ℝ) ^ d := by
  apply norm_rowTest_le
  intro t ht
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) (norm_shifted_log_div_le_half hR hc _)
  simpa only [Metric.mem_sphere, dist_zero_right] using ht.le

theorem period_center_radius_bound {K j : ℕ} (hK : 0 < K) (hj : j < K) :
    ‖(j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ + 3 / 4 ≤ (100 * (K : ℝ)) / 2 := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hjK : (j : ℝ) ≤ K := by exact_mod_cast hj.le
  have hnorm : ‖(j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ =
      (j : ℝ) * (2 * Real.pi) := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnorm]
  have hpi : 2 * Real.pi ≤ (8 : ℝ) := by linarith [Real.pi_lt_four]
  have hprod : (j : ℝ) * (2 * Real.pi) ≤ (K : ℝ) * 8 :=
    mul_le_mul hjK hpi (by positivity) (by positivity)
  linarith

theorem norm_exponentialMonomial_le_exp_budget (b h : ℂ) (d A : ℕ)
    {z : ℂ} {R H w0 wstar : ℝ} (hR : 1 ≤ R) (hH : 0 ≤ H)
    (hw0 : 0 < w0) (hws : 0 < wstar) (hz : ‖z‖ ≤ R)
    (hb : ‖b‖ ≤ (2 : ℝ) ^ A) (hh : ‖h‖ ≤ H / w0)
    (hd : d ≤ A) (hA : (A : ℝ) ≤ H / wstar) :
    ‖exponentialMonomial b h d z‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have h2R : 0 < 2 * R := by positivity
  have hlog : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  calc
    _ ≤ ‖b‖ * Real.exp (‖h‖ * R) * R ^ d := norm_exponentialMonomial_le b h d hR0 hz
    _ ≤ (2 : ℝ) ^ A * Real.exp ((H / w0) * R) * R ^ A := by
      apply mul_le_mul
      · exact mul_le_mul hb (Real.exp_le_exp.mpr
          (mul_le_mul hh le_rfl hR0 (div_nonneg hH hw0.le)))
          (Real.exp_pos _).le (by positivity)
      · exact pow_le_pow_right₀ hR hd
      · positivity
      · positivity
    _ = Real.exp ((H / w0) * R + (A : ℝ) * Real.log (2 * R)) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log h2R, mul_pow]
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have ha := mul_le_mul hA (le_refl _) hlog (div_nonneg hH hws.le)
      calc
        _ ≤ (H / w0) * R + (H / wstar) * Real.log (2 * R) := add_le_add le_rfl ha
        _ = _ := by ring

end PiExponent.AnalyticCollision

end OAI
