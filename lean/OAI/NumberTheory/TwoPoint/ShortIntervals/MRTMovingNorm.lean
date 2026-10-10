import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingStrip

namespace OAI

/-! Local growth uniformly at nearby centers gives a logarithmic-derivative
norm bound. The quantitative loss is B²/r, with no polynomial height loss. -/

namespace TwoPointCorrelations

open Complex
open scoped BigOperators Classical

/-- A local pair of growth bounds suffices for the actual logarithmic derivative
on the segment immediately to the right of one. -/
theorem mrt_moving_local_logderiv : ∃ K r₀ : ℝ, 0 < K ∧ 0 < r₀ ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q),
    ∀ (r t B σ : ℝ), 0 < r → r ≤ r₀ → 6 * r < |t| → 1 ≤ B →
      (∀ v : ℝ, |v - t| ≤ 3 * r →
        (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
          ‖mrtMovingLFunction χ r v z‖ ≤ Real.exp B) ∧
        (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
          ‖mrtMovingLFunction (χ ^ 2) r (2 * v) z‖ ≤ Real.exp B)) →
      1 < σ → σ ≤ 1 + r →
        ‖deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤ K * B ^ 2 / r := by
  obtain ⟨c, r₀, hc, hr₀, hstrip⟩ := mrt_moving_zero_free
  let P := 1 / Real.log ((15 / 16 : ℝ) / (7 / 8))
  have hP : 0 < P := by dsimp [P]; exact one_div_pos.mpr (Real.log_pos (by norm_num))
  let K := mrtCharacterLogDerivativeConstant / 3 + P / c
  have hK : 0 < K := by
    dsimp [K]
    exact add_pos (div_pos mrtCharacterLogDerivativeConstant_pos (by norm_num)) (div_pos hP hc)
  refine ⟨K, r₀, hK, hr₀, ?_⟩
  intro q _ χ r t B σ hr hrr ht hB hg hσ hσ2
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have ht3 : 3 * r < |t| := by linarith
  have hlocal := hg t (by simpa using (show 0 ≤ 3 * r by positivity))
  have hz := mrt_moving_real_point_norm hr (by linarith) hσ2
  have hn : DirichletCharacter.LFunction χ (mrtMovingPoint r t (mrtMovingRealPoint r σ)) ≠ 0 := by
    rw [mrt_moving_real_point hr]
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inr (by
      intro he; have hre := congrArg Complex.re he; simp at hre; linarith)) (by simpa using hσ.le)
  have hsep : ∀ ρ ∈ mrtDiskZeros (mrtMovingLFunction χ r t),
      c / (3 * B) ≤ ‖mrtMovingRealPoint r σ - ρ‖ := by
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
    have hβ : (mrtMovingPoint r t ρ).re < 1 - c * r / B := by
      by_contra! hh
      have he : (((mrtMovingPoint r t ρ).re : ℝ) : ℂ) + Complex.I * (v : ℂ) =
          mrtMovingPoint r t ρ := by dsimp [v]; apply Complex.ext <;> simp
      apply hstrip q χ r v B (mrtMovingPoint r t ρ).re hr hrr hvt hB
        (hg v hv).1 (hg v hv).2 hh
      rw [he]
      exact mrt_moving_zero_physical χ hr hρ
    have hgap : c * r / B ≤ σ - (mrtMovingPoint r t ρ).re := by linarith
    have hre : (mrtMovingRealPoint r σ - ρ).re =
        (σ - (mrtMovingPoint r t ρ).re) / (3 * r) := by
      simp only [Complex.sub_re, mrtMovingRealPoint, Complex.ofReal_re, mrtMovingPoint,
        Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
        zero_mul, mul_zero, sub_zero]
      field_simp
      ring
    calc
      _ = (c * r / B) / (3 * r) := by field_simp
      _ ≤ (σ - (mrtMovingPoint r t ρ).re) / (3 * r) :=
        div_le_div_of_nonneg_right hgap (by positivity)
      _ = (mrtMovingRealPoint r σ - ρ).re := hre.symm
      _ ≤ |(mrtMovingRealPoint r σ - ρ).re| := le_abs_self _
      _ ≤ _ := Complex.abs_re_le_norm _
  have hh := mrt_moving_logderiv_norm χ hr ht3 hBp hlocal.1 hz hn
    (show 0 < c / (3 * B) by positivity) hsep
  rw [mrt_moving_real_point hr] at hh
  apply hh.trans
  change ((mrtCharacterLogDerivativeConstant + P / (c / (3 * B))) * B) / (3 * r) ≤ _
  have hmul : mrtCharacterLogDerivativeConstant * B ≤ mrtCharacterLogDerivativeConstant * B ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith : B ≤ B ^ 2) mrtCharacterLogDerivativeConstant_pos.le
  have heq : P / (c / (3 * B)) = 3 * P * B / c := by field_simp
  rw [heq]
  have halg : (mrtCharacterLogDerivativeConstant + 3 * P * B / c) * B / (3 * r) =
      (mrtCharacterLogDerivativeConstant * B / 3 + (P / c) * B ^ 2) / r := by ring
  rw [halg]
  apply div_le_div_of_nonneg_right _ hr.le
  dsimp [K]
  nlinarith only [hmul]

end TwoPointCorrelations

end OAI
