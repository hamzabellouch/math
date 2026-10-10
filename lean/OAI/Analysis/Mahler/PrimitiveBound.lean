import OAI.Analysis.Mahler.SineBound
import OAI.Analysis.Mahler.RadialBridge

namespace OAI

namespace SymmetricMahler
open Real Set MeasureTheory

/-- Dividing the sine lower bound yields the exact residual reciprocal estimate. -/
theorem sine_reciprocal_bound {r θ Δ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hΔ : 0 < Δ) (hsine : sqrt ((1-r^2)*Δ/r) ≤ sin θ) :
    (1-r^2)/(r*sin θ) ≤ sqrt (1-r^2)/(sqrt r*sqrt Δ) := by
  have hden : 0 < 1-r^2 := by nlinarith
  have hroot : 0 < sqrt ((1-r^2)*Δ/r) := sqrt_pos.2 (by positivity)
  have hs : 0 < sin θ := hroot.trans_le hsine
  calc
    _ ≤ (1-r^2)/(r*sqrt ((1-r^2)*Δ/r)) := by
      apply div_le_div_of_nonneg_left hden.le (by positivity)
      exact mul_le_mul_of_nonneg_left hsine hr.le
    _ = sqrt (1-r^2)/(sqrt r*sqrt Δ) := by
      rw [sqrt_div (mul_nonneg hden.le hΔ.le), sqrt_mul hden.le]
      have hr2 := sq_sqrt hr.le
      have hd2 := sq_sqrt hden.le
      field_simp
      nlinarith

/-- The reciprocal angular-speed estimate converts to the
error-integral density, with the explicit coefficient π. -/
theorem radial_primitive_density_bound {r θ Δ m : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hm : 0 ≤ m) (hΔ : 0 < Δ)
    (hsine : sqrt ((1-r^2)*Δ/r) ≤ sin θ) :
    (4*m/Real.pi)*(r^(2*m-1 : ℝ)/angularSpeed r θ) ≤
      2*m*r^(2*m-1 : ℝ) +
      Real.pi*(m*r^(2*m-3/2 : ℝ)*sqrt (1-r^2)/sqrt Δ) := by
  have hden : 0 < 1-r^2 := by nlinarith
  have hs : 0 < sin θ := (sqrt_pos.2 (show 0 < (1-r^2)*Δ/r by positivity)).trans_le hsine
  have hi := angular_speed_inverse_bound hr hr1 hs
  have hi' := sine_reciprocal_bound hr hr1 hΔ hsine
  have hrecip : 1/angularSpeed r θ ≤ Real.pi/2 +
      (Real.pi^2/4)*(sqrt (1-r^2)/(sqrt r*sqrt Δ)) := by
    have hh := mul_le_mul_of_nonneg_left hi' (show 0 ≤ Real.pi^2/4 by positivity)
    linarith
  have hpow : r^(2*m-1 : ℝ)/sqrt r = r^(2*m-3/2 : ℝ) := by
    rw [sqrt_eq_rpow, ← rpow_sub hr]
    congr 1
    ring
  calc
    _ = ((4*m/Real.pi)*r^(2*m-1 : ℝ))*(1/angularSpeed r θ) := by ring
    _ ≤ ((4*m/Real.pi)*r^(2*m-1 : ℝ))*(Real.pi/2 +
        (Real.pi^2/4)*(sqrt (1-r^2)/(sqrt r*sqrt Δ))) :=
      mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ = 2*m*r^(2*m-1 : ℝ) +
        Real.pi*m*(r^(2*m-1 : ℝ)/sqrt r)*sqrt (1-r^2)/sqrt Δ := by
      field_simp
      ; ring
    _ = _ := by rw [hpow]; ring

/-- The radial form of the vertical primitive, before proving its equality
with the integral in the image domain. -/
noncomputable def radialPrimitiveDensity (θ : ℝ → ℝ) (m r : ℝ) : ℝ :=
  (4*m/Real.pi)*(r^(2*m-1 : ℝ)/angularSpeed r (θ r))

lemma radial_error_integrable {m r₀ : ℝ} (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hr₀1 : r₀ < 1) :
    IntervalIntegrable (errorIntegrand radialMap r₀ m) volume r₀ 1 :=
  (uniform_error_bound measurable_radialMap continuousOn_radialMap
    (fun _ hr => hasDerivAt_radialMap hr.1 hr.2) hm hr₀ hr₀1).1

/-- The density is integrable through the potentially singular initial radius;
the square-root sine bound, rather than an assumed endpoint regularity, controls it. -/
theorem radial_primitive_integrable {θ : ℝ → ℝ} {m r₀ s : ℝ}
    (hθ : Measurable θ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hr₀s : r₀ ≤ s) (hs1 : s < 1)
    (hsine : ∀ r ∈ Ioo r₀ 1,
      sqrt ((1-r^2)*(radialMap r-radialMap r₀)/r) ≤ sin (θ r)) :
    IntervalIntegrable (radialPrimitiveDensity θ m) volume r₀ s := by
  have hr₀1 : r₀ < 1 := hr₀s.trans_lt hs1
  have herr := (radial_error_integrable hm hr₀ hr₀1).mono_set
    (show uIcc r₀ s ⊆ uIcc r₀ 1 by
      rw [uIcc_of_le hr₀s, uIcc_of_le hr₀1.le]
      exact Icc_subset_Icc le_rfl hs1.le)
  have hpow : IntervalIntegrable (fun r : ℝ => 2*m*r^(2*m-1 : ℝ)) volume r₀ s :=
    (intervalIntegral.intervalIntegrable_rpow (Or.inl (by linarith))).const_mul (2*m)
  have hmajor := hpow.add (herr.const_mul Real.pi)
  have hmeas : Measurable (radialPrimitiveDensity θ m) := by
    unfold radialPrimitiveDensity angularSpeed
    fun_prop
  apply hmajor.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
  rw [uIoc_of_le hr₀s] at hr
  have hrpos : 0 < r := hr₀.trans_lt hr.1
  have hr1 : r < 1 := hr.2.trans_lt hs1
  have hΔ : 0 < radialMap r-radialMap r₀ :=
    sub_pos.mpr (strictMonoOn_radialMap ⟨hr₀,hr₀1⟩ ⟨hrpos.le,hr1⟩ hr.1)
  have hs := hsine r ⟨hr.1,hr1⟩
  have hsin : 0 < sin (θ r) :=
    (sqrt_pos.2 (show 0 < (1-r^2)*(radialMap r-radialMap r₀)/r by
      have : 0 < 1-r^2 := by nlinarith
      positivity)).trans_le hs
  have hn : 0 ≤ radialPrimitiveDensity θ m r := by
    unfold radialPrimitiveDensity angularSpeed
    have : 0 < 1-r^2 := by nlinarith
    have : 0 < arctan (2*r*sin (θ r)/(1-r^2)) := arctan_pos.mpr (by positivity)
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact radial_primitive_density_bound hrpos hr1 (by linarith) hΔ hs

/-- The leading term of the radial primitive integrates with coefficient exactly one. -/
theorem integral_radial_leading {m a b : ℝ} (hm : 0 < m) :
    (∫ r in a..b, 2*m*r^(2*m-1 : ℝ)) = b^(2*m : ℝ)-a^(2*m : ℝ) := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
  have he : 2*m-1+1 = 2*m := by ring
  rw [he]
  field_simp

/-- The radial primitive is bounded by s^(2m) plus π times the
uniformly controlled error. This bound does not assert equality
with the image-domain primitive. -/
theorem radial_primitive_integral_bound {θ : ℝ → ℝ} {m r₀ s : ℝ}
    (hθ : Measurable θ) (hm : 2 ≤ m) (hr₀ : 0 ≤ r₀) (hr₀s : r₀ ≤ s) (hs1 : s < 1)
    (hsine : ∀ r ∈ Ioo r₀ 1,
      sqrt ((1-r^2)*(radialMap r-radialMap r₀)/r) ≤ sin (θ r)) :
    (∫ r in r₀..s, radialPrimitiveDensity θ m r) ≤
      s^(2*m : ℝ) + Real.pi*(∫ r in r₀..(1 : ℝ), errorIntegrand radialMap r₀ m r) := by
  have hr₀1 : r₀ < 1 := hr₀s.trans_lt hs1
  have herr := radial_error_integrable hm hr₀ hr₀1
  have herr' := herr.mono_set
    (show uIcc r₀ s ⊆ uIcc r₀ 1 by
      rw [uIcc_of_le hr₀s, uIcc_of_le hr₀1.le]
      exact Icc_subset_Icc le_rfl hs1.le)
  have hpow : IntervalIntegrable (fun r : ℝ => 2*m*r^(2*m-1 : ℝ)) volume r₀ s :=
    (intervalIntegral.intervalIntegrable_rpow (Or.inl (by linarith))).const_mul (2*m)
  have hcompare : (∫ r in r₀..s, radialPrimitiveDensity θ m r) ≤
      (∫ r in r₀..s, 2*m*r^(2*m-1 : ℝ) + Real.pi*errorIntegrand radialMap r₀ m r) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hr₀s
      (radial_primitive_integrable hθ hm hr₀ hr₀s hs1 hsine) (hpow.add (herr'.const_mul Real.pi))
    intro r hr
    have hrpos : 0 < r := hr₀.trans_lt hr.1
    have hr1 : r < 1 := hr.2.trans hs1
    have hΔ : 0 < radialMap r-radialMap r₀ :=
      sub_pos.mpr (strictMonoOn_radialMap ⟨hr₀,hr₀1⟩ ⟨hrpos.le,hr1⟩ hr.1)
    exact radial_primitive_density_bound hrpos hr1 (by linarith) hΔ (hsine r ⟨hr.1,hr1⟩)
  rw [intervalIntegral.integral_add hpow (herr'.const_mul Real.pi),
    integral_radial_leading (show 0 < m by linarith), intervalIntegral.integral_const_mul] at hcompare
  have herrmono : (∫ r in r₀..s, errorIntegrand radialMap r₀ m r) ≤
      (∫ r in r₀..(1 : ℝ), errorIntegrand radialMap r₀ m r) := by
    apply intervalIntegral.integral_mono_interval le_rfl hr₀s hs1.le _ herr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    unfold errorIntegrand
    have hrpos : 0 ≤ r := hr₀.trans hr.1.le
    positivity
  have hnonneg : 0 ≤ r₀^(2*m : ℝ) := rpow_nonneg hr₀ _
  nlinarith [mul_le_mul_of_nonneg_left herrmono Real.pi_pos.le]

/-- Uniform small error for every measurable angular fiber satisfying the
proved sine condition. The threshold is independent of the basepoint and fiber. -/
theorem radial_primitive_uniform_small {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℝ, ∀ m : ℝ, m₀ ≤ m → ∀ r₀ ∈ Ico (0 : ℝ) 1,
      ∀ θ : ℝ → ℝ, Measurable θ →
        (∀ r ∈ Ioo r₀ 1,
          sqrt ((1-r^2)*(radialMap r-radialMap r₀)/r) ≤ sin (θ r)) →
        ∀ s ∈ Ico r₀ 1,
          IntervalIntegrable (radialPrimitiveDensity θ m) volume r₀ s ∧
          (∫ r in r₀..s, radialPrimitiveDensity θ m r) < s^(2*m : ℝ)+ε := by
  obtain ⟨m₀, hm₀⟩ := conformal_radial_error_small (show 0 < ε/Real.pi by positivity)
  refine ⟨max m₀ 2, ?_⟩
  intro m hm r₀ hr₀ θ hθ hsine s hs
  have hm2 : 2 ≤ m := (le_max_right m₀ 2).trans hm
  have he := (hm₀ m ((le_max_left m₀ 2).trans hm) r₀ hr₀).2
  have hp := radial_primitive_integral_bound hθ hm2 hr₀.1 hs.1 hs.2 hsine
  refine ⟨radial_primitive_integrable hθ hm2 hr₀.1 hs.1 hs.2 hsine, ?_⟩
  have he' : Real.pi*(∫ r in r₀..(1 : ℝ), errorIntegrand radialMap r₀ m r) < ε := by
    have h := mul_lt_mul_of_pos_left he Real.pi_pos
    have heq : Real.pi*(ε/Real.pi) = ε := by field_simp
    rwa [heq] at h
  linarith

end SymmetricMahler

end OAI
