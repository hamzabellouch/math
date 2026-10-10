import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingNorm

namespace OAI

/-! The shrinking-disk estimate inside a narrower zero-free strip. This
extension to the left of one is used for the smoothed Mangoldt contour. -/

namespace TwoPointCorrelations

open Complex
open scoped Classical

theorem mrt_moving_strip_logderiv : ∃ c K r₀ : ℝ, 0 < c ∧ 0 < K ∧ 0 < r₀ ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q),
    ∀ (r t B σ : ℝ), 0 < r → r ≤ r₀ → 6 * r < |t| → 1 ≤ B →
      (∀ v : ℝ, |v - t| ≤ 3 * r →
        (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
          ‖mrtMovingLFunction χ r v z‖ ≤ Real.exp B) ∧
        (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
          ‖mrtMovingLFunction (χ ^ 2) r (2 * v) z‖ ≤ Real.exp B)) →
      1 - c * r / B ≤ σ → σ ≤ 1 + r →
        DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ)) ≠ 0 ∧
        ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ K * B ^ 2 / r := by
  obtain ⟨c₀, r₀, hc₀, hr₀, hstrip⟩ := mrt_moving_zero_free
  let d := min c₀ (1 / 2)
  let P := 1 / Real.log ((15 / 16 : ℝ) / (7 / 8))
  let K := mrtCharacterLogDerivativeConstant / 3 + 2 * P / d
  have hd : 0 < d := lt_min hc₀ (by norm_num)
  have hdc : d ≤ c₀ := min_le_left _ _
  have hdhalf : d ≤ 1 / 2 := min_le_right _ _
  have hP : 0 < P := by dsimp [P]; exact one_div_pos.mpr (Real.log_pos (by norm_num))
  have hK : 0 < K := by
    dsimp [K]
    exact add_pos (div_pos mrtCharacterLogDerivativeConstant_pos (by norm_num)) (by positivity)
  refine ⟨d / 2, K, r₀, by positivity, hK, hr₀, ?_⟩
  intro q _ χ r t B σ hr hrr ht hB hg hσ hσ2
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have ht3 : 3 * r < |t| := by linarith
  have hlocal := hg t (by simpa using (show 0 ≤ 3 * r by positivity))
  have hdelt : (d / 2) * r / B = (d * r / B) / 2 := by ring
  have hdcost : d * r / B ≤ c₀ * r / B :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hdc hr.le) hBp.le
  have hdz : 0 ≤ d * r / B := by positivity
  have hn : DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
    apply hstrip q χ r t B σ hr hrr ht3 hB hlocal.1 hlocal.2
    rw [hdelt] at hσ
    linarith
  have hrad : (d / 2) * r / B ≤ r / 4 := by
    have hnumer : (d / 2) * r ≤ r / 4 := by nlinarith
    exact (div_le_div_of_nonneg_right hnumer hBp.le).trans
      (div_le_self (by positivity) hB)
  have hz := mrt_moving_real_point_norm hr (by linarith) hσ2
  have hn' : DirichletCharacter.LFunction χ (mrtMovingPoint r t (mrtMovingRealPoint r σ)) ≠ 0 := by
    rwa [mrt_moving_real_point hr]
  have hsep : ∀ ρ ∈ mrtDiskZeros (mrtMovingLFunction χ r t),
      d / (6 * B) ≤ ‖mrtMovingRealPoint r σ - ρ‖ := by
    intro ρ hρ
    have hρn : ‖ρ‖ ≤ 7 / 8 := by simpa using hρ.1
    let v := (mrtMovingPoint r t ρ).im
    have hv : |v - t| ≤ 3 * r := by
      have hi := (Complex.abs_im_le_norm ρ).trans (hρn.trans (by norm_num : (7 / 8 : ℝ) ≤ 1))
      have he : v - t = 3 * r * ρ.im := by
        dsimp [v, mrtMovingPoint]
        simp only [Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, mul_zero, zero_add, add_zero]
        ring
      rw [he, abs_mul, abs_of_pos (by positivity : 0 < 3 * r)]
      nlinarith
    have hvt : 3 * r < |v| := by
      have hh := abs_add_le (t - v) v
      rw [sub_add_cancel, abs_sub_comm] at hh
      linarith
    have hβ : (mrtMovingPoint r t ρ).re < 1 - c₀ * r / B := by
      by_contra! hh
      have he : (((mrtMovingPoint r t ρ).re : ℝ) : ℂ) + Complex.I * (v : ℂ) =
          mrtMovingPoint r t ρ := by dsimp [v]; apply Complex.ext <;> simp
      apply hstrip q χ r v B (mrtMovingPoint r t ρ).re hr hrr hvt hB
        (hg v hv).1 (hg v hv).2 hh
      rw [he]
      exact mrt_moving_zero_physical χ hr hρ
    have hgap : (d * r / B) / 2 ≤ σ - (mrtMovingPoint r t ρ).re := by
      rw [hdelt] at hσ
      linarith
    have hre : (mrtMovingRealPoint r σ - ρ).re =
        (σ - (mrtMovingPoint r t ρ).re) / (3 * r) := by
      simp only [Complex.sub_re, mrtMovingRealPoint, Complex.ofReal_re, mrtMovingPoint,
        Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
        zero_mul, mul_zero, sub_zero]
      field_simp
      ring
    calc
      _ = ((d * r / B) / 2) / (3 * r) := by field_simp; norm_num
      _ ≤ (σ - (mrtMovingPoint r t ρ).re) / (3 * r) :=
        div_le_div_of_nonneg_right hgap (by positivity)
      _ = (mrtMovingRealPoint r σ - ρ).re := hre.symm
      _ ≤ |(mrtMovingRealPoint r σ - ρ).re| := le_abs_self _
      _ ≤ _ := Complex.abs_re_le_norm _
  have hh := mrt_moving_logderiv_norm χ hr ht3 hBp hlocal.1 hz hn'
    (show 0 < d / (6 * B) by positivity) hsep
  rw [mrt_moving_real_point hr] at hh
  refine ⟨hn, hh.trans ?_⟩
  change ((mrtCharacterLogDerivativeConstant + P / (d / (6 * B))) * B) / (3 * r) ≤ _
  have hmul : mrtCharacterLogDerivativeConstant * B ≤ mrtCharacterLogDerivativeConstant * B ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith : B ≤ B ^ 2) mrtCharacterLogDerivativeConstant_pos.le
  have heq : P / (d / (6 * B)) = 6 * P * B / d := by field_simp
  rw [heq]
  have halg : (mrtCharacterLogDerivativeConstant + 6 * P * B / d) * B / (3 * r) =
      (mrtCharacterLogDerivativeConstant * B / 3 + (2 * P / d) * B ^ 2) / r := by ring
  rw [halg]
  apply div_le_div_of_nonneg_right _ hr.le
  dsimp [K]
  nlinarith only [hmul]

end TwoPointCorrelations

end OAI
