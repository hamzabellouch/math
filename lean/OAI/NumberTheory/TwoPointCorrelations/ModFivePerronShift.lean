import OAI.NumberTheory.TwoPointCorrelations.ModFiveRectangleShift

namespace OAI

/-! Quantitative finite contour shift for the actual twisted Mangoldt
integrand. The left side stays inside the proved zero-free rectangle and
the two horizontal sides are bounded explicitly.
-/

namespace TwoPointCorrelations

open Complex Set Erdos970

noncomputable def modFivePerronIntegrand (χ : DirichletCharacter ℂ 5)
    (x : ℝ) (s : ℂ) : ℂ :=
  (-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
    modFivePerronKernel x s

theorem modFive_finite_perron_shift : ∃ a C : ℝ,
    0 < a ∧ a ≤ 1 / 4 ∧ 0 < C ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ T x b : ℝ,
      2 ≤ T → 1 ≤ x → 1 - a / Real.log (T + 2) ≤ b → b ≤ 2 →
      ‖VIntegral (modFivePerronIntegrand χ x) b (-T) T‖ ≤
        4 * Real.pi * C * Real.log (T + 2) ^ 2 * x ^ (1 - a / Real.log (T + 2)) +
          2 * (b - (1 - a / Real.log (T + 2))) *
            (C * Real.log (T + 2) ^ 2 * x ^ b / T ^ 2) := by
  obtain ⟨a, C, ha, ha4, hC, hreg⟩ := modFive_logderiv_rectangles
  refine ⟨a, C, ha, ha4, hC, ?_⟩
  intro χ hχ T x b hT hx hab hb2
  let A := 1 - a / Real.log (T + 2)
  let H := Real.log (T + 2)
  have hTp : 0 < T := by linarith
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hH : 0 < H := Real.log_pos (by linarith)
  have hHhalf : 1 / 2 ≤ H := by
    simpa only [abs_of_nonneg hTp.le] using modFive_log_height_ge_half T
  have hAhalf : 1 / 2 ≤ A := by
    have hadiv : a / H ≤ 1 / 2 := by
      apply (div_le_iff₀ hH).mpr
      linarith
    dsimp [A, H] at *
    linarith
  have heval (σ t : ℝ) (hσ : A ≤ σ) (hσ2 : σ ≤ 2) (ht : |t| ≤ T) :
      DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
      ‖-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * H ^ 2 := by
    have he := hreg χ hχ T hT ((σ : ℂ) + (t : ℂ) * Complex.I)
      (by
        have hr : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
        rw [hr]
        exact hσ) (by simpa using hσ2) (by simpa using ht)
    exact ⟨he.1, by simpa only [neg_div, norm_neg] using he.2⟩
  have hf : DifferentiableOn ℂ (modFivePerronIntegrand χ x)
      (Rectangle ((A : ℂ) - Complex.I * (T : ℂ)) ((b : ℂ) + Complex.I * (T : ℂ))) := by
    intro s hs
    have hab' : A ≤ b := hab
    have hs' : s.re ∈ Icc A b ∧ s.im ∈ Icc (-T) T := by
      simpa [Rectangle, Complex.mem_reProdIm, uIcc_of_le hab', uIcc_of_le (show -T ≤ T by linarith)] using hs
    have hn := (hreg χ hχ T hT s hs'.1.1 (hs'.1.2.trans hb2) (abs_le.mpr hs'.2)).1
    have hs0 : s ≠ 0 := by
      intro he
      have hre := hs'.1.1
      rw [he] at hre
      simp only [Complex.zero_re] at hre
      linarith
    have hs1 : s + 1 ≠ 0 := by
      intro he
      have hre := congrArg Complex.re he
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
      linarith [hs'.1.1]
    exact (modFive_perron_integrand_differentiableAt χ hχ hxp hn hs0 hs1).differentiableWithinAt
  have hside (t : ℝ) (ht : |t| = T) :
      ∀ σ ∈ Icc A b, ‖modFivePerronIntegrand χ x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * H ^ 2 * x ^ b / T ^ 2 := by
    intro σ hσ
    have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
    have ht2 : t ^ 2 = T ^ 2 := by rw [← sq_abs, ht]
    have hlog := (heval σ t hσ.1 (hσ.2.trans hb2) ht.le).2
    have hk := modFive_perron_kernel_horizontal hxp σ ht0
    have hpow : x ^ σ ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx hσ.2
    calc
      _ = ‖-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
            ‖modFivePerronKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_mul _ _
      _ ≤ (C * H ^ 2) * (x ^ σ / t ^ 2) :=
        mul_le_mul hlog hk (norm_nonneg _) (mul_nonneg hC.le (sq_nonneg H))
      _ ≤ _ := by
        rw [ht2, ← mul_div_assoc]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow
          (mul_nonneg hC.le (sq_nonneg H))) (sq_nonneg T)
  have hv : ‖VIntegral (modFivePerronIntegrand χ x) A (-T) T‖ ≤
      (4 * C * H ^ 2 * x ^ A) * Real.pi := by
    apply modFive_vertical_quadratic_bound hTp.le (by positivity)
    intro t ht
    have hlog := (heval A t le_rfl (hab.trans hb2) (abs_le.mpr ht)).2
    have hk := modFive_perron_kernel_vertical hxp hAhalf t
    calc
      _ = ‖-deriv (DirichletCharacter.LFunction χ) ((A : ℂ) + (t : ℂ) * Complex.I) /
          DirichletCharacter.LFunction χ ((A : ℂ) + (t : ℂ) * Complex.I)‖ *
            ‖modFivePerronKernel x ((A : ℂ) + (t : ℂ) * Complex.I)‖ := norm_mul _ _
      _ ≤ (C * H ^ 2) * (4 * x ^ A / (1 + t ^ 2)) :=
        mul_le_mul hlog hk (norm_nonneg _) (mul_nonneg hC.le (sq_nonneg H))
      _ = _ := by ring
  have hs := modFive_rectangle_shift_bound hab hf
    (hside T (abs_of_nonneg hTp.le)) (hside (-T) (by simp [abs_of_nonneg hTp.le]))
  calc
    _ ≤ (4 * C * H ^ 2 * x ^ A) * Real.pi +
        2 * (C * H ^ 2 * x ^ b / T ^ 2) * (b - A) :=
      hs.trans (add_le_add hv le_rfl)
    _ = _ := by dsimp [A, H]; ring

end TwoPointCorrelations

end OAI
