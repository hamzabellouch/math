import OAI.NumberTheory.TwoPoint.Halasz.HalaszLogOscillation

namespace OAI

/-! A first-derivative oscillatory-integral estimate for the logarithmic
phase, to be used on the nonstationary pieces of the Poisson kernel. -/

namespace TwoPointCorrelations

open MeasureTheory

lemma halasz_log_phase_continuousOn (u v a b : ℝ) (ha : 0 < a) :
    ContinuousOn (halaszLogPhase u v) (Set.Icc a b) := by
  intro x hx
  exact (halasz_log_phase_deriv u v x (ha.trans_le hx.1).ne').continuousAt.continuousWithinAt

lemma halasz_log_reciprocal_deriv_continuousOn (u v a b : ℝ) (ha : 0 < a)
    (hd : ∀ x ∈ Set.Icc a b, halaszLogSlope u v x ≠ 0) :
    ContinuousOn (halaszLogReciprocalDeriv u v) (Set.Icc a b) := by
  have hx (x : ℝ) (h : x ∈ Set.Icc a b) : x ≠ 0 := (ha.trans_le h.1).ne'
  apply continuousOn_const.div
    ((continuousOn_id.pow 2).mul (((continuousOn_const.div continuousOn_id hx).sub
      continuousOn_const).pow 2))
  intro x h
  exact mul_ne_zero (pow_ne_zero 2 (hx x h)) (pow_ne_zero 2 (hd x h))

theorem halasz_log_first_derivative (u v a b lam : ℝ) (hu : 0 ≤ u)
    (ha : 0 < a) (hab : a ≤ b) (hlam : 0 < lam)
    (hslope : ∀ x ∈ Set.Icc a b, lam ≤ |halaszLogSlope u v x|) :
    ‖∫ x in a..b, halaszLogPhase u v x‖ ≤ 4/lam := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc a b) : halaszLogSlope u v x ≠ 0 := by
    have hh := hslope x hx
    exact abs_pos.mp (hlam.trans_le hh)
  have hiF : IntervalIntegrable (halaszLogPhase u v) volume a b := (halasz_log_phase_continuousOn u v a b ha).intervalIntegrable_of_Icc hab
  let K : ℝ → ℂ := fun x => Complex.I*halaszLogPhase u v x*
    (halaszLogReciprocalDeriv u v x:ℂ)
  have hiK : IntervalIntegrable K volume a b :=
    ((continuousOn_const.mul (halasz_log_phase_continuousOn u v a b ha)).mul
      (Complex.continuous_ofReal.comp_continuousOn
        (halasz_log_reciprocal_deriv_continuousOn u v a b ha hd))).intervalIntegrable_of_Icc hab
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => halasz_log_phase_primitive_deriv u v x
      (ha.trans_le (show x ∈ Set.Icc a b from by simpa only [Set.uIcc_of_le hab] using hx).1).ne'
      (hd x (by simpa only [Set.uIcc_of_le hab] using hx))) (hiF.sub hiK)
  have hKn (x : ℝ) : ‖K x‖ = halaszLogReciprocalDeriv u v x := by
    simp only [K, norm_mul, Complex.norm_I, one_mul, halasz_log_phase_norm,
      Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by unfold halaszLogReciprocalDeriv; positivity)
  have hKI : ‖∫ x in a..b, K x‖ ≤
      (halaszLogSlope u v b)⁻¹-(halaszLogSlope u v a)⁻¹ := by
    have hh := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := K) hab
    simp_rw [hKn] at hh
    rwa [halasz_log_reciprocal_integral u v a b ha hab hd] at hh
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |(halaszLogSlope u v x)⁻¹| ≤ 1/lam := by
    rw [abs_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hlam (hslope x hx)
  have hBa := hbound a ⟨le_rfl, hab⟩
  have hBb := hbound b ⟨hab, le_rfl⟩
  have hR : (halaszLogSlope u v b)⁻¹-(halaszLogSlope u v a)⁻¹ ≤ 2/lam := by
    have haa := le_abs_self (-(halaszLogSlope u v a)⁻¹)
    rw [abs_neg] at haa
    have hbb := le_abs_self ((halaszLogSlope u v b)⁻¹)
    simp only [div_eq_mul_inv] at hBa hBb ⊢
    linarith
  have hHnorm (x : ℝ) :
      ‖-Complex.I*halaszLogPhase u v x*((halaszLogSlope u v x)⁻¹:ℝ)‖ =
        |(halaszLogSlope u v x)⁻¹| := by
    simp only [norm_mul, norm_neg, Complex.norm_I, halasz_log_phase_norm,
      one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hidentity : (∫ x in a..b, halaszLogPhase u v x) =
      -Complex.I*halaszLogPhase u v b*((halaszLogSlope u v b)⁻¹:ℝ) -
      (-Complex.I*halaszLogPhase u v a*((halaszLogSlope u v a)⁻¹:ℝ)) +
      ∫ x in a..b, K x := by
    rw [intervalIntegral.integral_sub hiF hiK] at hFTC
    exact sub_eq_iff_eq_add.mp hFTC
  rw [hidentity]
  apply (norm_add_le _ _).trans
  have hh := norm_sub_le
    (-Complex.I*halaszLogPhase u v b*((halaszLogSlope u v b)⁻¹:ℝ))
    (-Complex.I*halaszLogPhase u v a*((halaszLogSlope u v a)⁻¹:ℝ))
  simp only [hHnorm] at hh
  simp only [div_eq_mul_inv] at hBa hBb hR ⊢
  linarith

end TwoPointCorrelations

end OAI
