import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningWeightLimit

namespace OAI

/-! A bounded physical outgoing norm gives bounded rescaled Cauchy data at
any fixed positive oscillatory cutoff. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_rescaled_data_bounded
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (M G C : ℝ) (hM : 0 < M)
    (q : ℕ → ℝ → ℂ × ℂ) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8 + 2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1)
    (hbound : ∀ᶠ n in atTop, spectralShellNorm
      (Real.sqrt ‖spectralLiouvilleMomentum 1 h (b n) (eta n) (omega n) (gamma n)
        (r₀ n+d n*M)‖) (q n (r₀ n+d n*M)) ≤ C) :
    ∃ B : ℝ, ∀ᶠ n in atTop,
      ‖spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n) (-M)‖ ≤ B := by
  let k₀ := Real.sqrt (Real.sqrt M)
  have hk₀ : 0 < k₀ := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hM)
  let k := fun n => Real.sqrt ‖spectralLiouvilleMomentum 1 h (b n) (eta n) (omega n)
    (gamma n) (r₀ n+d n*M)‖
  have hw := spectralTurning_weight_tendsto h b eta omega gamma r₀ d M G hM.le hr₀ hdata
  have hlow : k₀/2 < k₀ := by linarith
  have hupp : k₀ < 2*k₀ := by linarith
  refine ⟨max (k₀/2)⁻¹ (2*k₀)*C,?_⟩
  filter_upwards [hdata,hbound,hw.eventually (lt_mem_nhds hlow),
    hw.eventually (gt_mem_nhds hupp)] with n hn hb hl hu
  have hd : 0 < d n := by
    apply lt_of_le_of_ne hn.2.1
    intro he
    have hh := hn.2.2.2.2.2
    rw [← he] at hh
    norm_num at hh
  have hs : 0 < Real.sqrt (d n) := Real.sqrt_pos.mpr hd
  have hk : 0 < k n := by
    have hn0 : 0 ≤ k n := Real.sqrt_nonneg _
    change k₀/2 < Real.sqrt (d n)*k n at hl
    nlinarith
  have he : spectralShellNorm (Real.sqrt (d n)*k n)
      (spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n) (-M)) =
      spectralShellNorm (k n) (q n (r₀ n+d n*M)) := by
    simpa only [spectralTurningAiryState,spectralScalarReflect,spectralTurningState,
      zero_add,zero_sub,neg_neg,neg_mul] using
      spectralShellNorm_scale (Real.sqrt (d n)) (k n) hs hk (q n (r₀ n+d n*M))
  calc
    _ ≤ max (k₀/2)⁻¹ (2*k₀) * spectralShellNorm (Real.sqrt (d n)*k n)
        (spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n) (-M)) :=
      spectralShellNorm_controls_norm (k₀/2) (2*k₀) _ (half_pos hk₀) hl.le hu.le _
    _ = max (k₀/2)⁻¹ (2*k₀) * spectralShellNorm (k n) (q n (r₀ n+d n*M)) := by rw [he]
    _ ≤ max (k₀/2)⁻¹ (2*k₀)*C := mul_le_mul_of_nonneg_left hb (by positivity)

end DefocusingNLS

end OAI
