import OAI.NumberTheory.TwoPoint.Fourier.ModFiveVerticalTails

namespace OAI

/-! A finite quantitative contour bound for the actual smoothed twisted
Mangoldt sums, using the zero-free region and the inverse-square tail
estimate. -/

namespace TwoPointCorrelations

open Complex Erdos970

lemma modFive_perron_normalization : ‖(1 / (2 * Real.pi * Complex.I) : ℂ)‖ ≤ 1 := by
  have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  simp only [norm_div, norm_one, norm_mul, norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_I, mul_one]
  exact (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr hp

theorem modFive_smoothed_contour_bound : ∃ a C D : ℝ,
    0 < a ∧ a ≤ 1 / 4 ∧ 0 < C ∧ 0 < D ∧
    ∀ (χ : DirichletCharacter ℂ 5), χ ≠ 1 → ∀ T x δ : ℝ,
      2 ≤ T → 1 ≤ x → 0 < δ → δ ≤ 1 →
      (∀ n : ℕ, x ≠ (n : ℝ)) →
      ‖modFiveSmoothedPsi χ x‖ ≤
        4 * Real.pi * C * Real.log (T + 2) ^ 2 * x ^ (1 - a / Real.log (T + 2)) +
          4 * C * Real.log (T + 2) ^ 2 * x ^ (1 + δ) / T ^ 2 +
          2 * (1 / δ + D) * x ^ (1 + δ) / T := by
  obtain ⟨a, C, ha, ha4, hC, hfinite⟩ := modFive_finite_perron_shift
  obtain ⟨D, hD, htail⟩ := modFive_perron_tail_bound
  refine ⟨a, C, D, ha, ha4, hC, hD, ?_⟩
  intro χ hχ T x δ hT hx hδ hδ1 hxnat
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hH : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
  have hleft : 1 - a / Real.log (T + 2) ≤ 1 + δ := by
    have hd := div_nonneg ha.le hH.le
    linarith
  have hfin := hfinite χ hχ T x (1 + δ) hT hx hleft (by linarith)
  have hta := htail χ hχ δ x T hδ hxpos (by linarith)
  have hlength : 1 + δ - (1 - a / Real.log (T + 2)) ≤ 2 := by
    have hlog : 1 / 2 ≤ Real.log (T + 2) := by
      simpa only [abs_of_nonneg (by linarith : 0 ≤ T)] using modFive_log_height_ge_half T
    have hdiv : a / Real.log (T + 2) ≤ 1 := (div_le_one hH).mpr (by linarith)
    linarith
  have hfin' : ‖VIntegral (modFivePerronIntegrand χ x) (1 + δ) (-T) T‖ ≤
      4 * Real.pi * C * Real.log (T + 2) ^ 2 * x ^ (1 - a / Real.log (T + 2)) +
        4 * C * Real.log (T + 2) ^ 2 * x ^ (1 + δ) / T ^ 2 := by
    apply hfin.trans
    apply add_le_add le_rfl
    calc
      _ ≤ 2 * 2 * (C * Real.log (T + 2) ^ 2 * x ^ (1 + δ) / T ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength (by norm_num))
          (by positivity)
      _ = _ := by ring
  have hvert : ‖VerticalIntegral (modFivePerronIntegrand χ x) (1 + δ)‖ ≤
      ‖VIntegral (modFivePerronIntegrand χ x) (1 + δ) (-T) T‖ +
        2 * (1 / δ + D) * x ^ (1 + δ) / T := by
    exact (norm_le_insert' _ _).trans (add_le_add le_rfl hta)
  rw [modFiveSmoothedPsi_perron χ hxpos (by linarith : 1 < 1 + δ) hxnat]
  change ‖(1 / (2 * Real.pi * Complex.I)) •
    VerticalIntegral (modFivePerronIntegrand χ x) (1 + δ)‖ ≤ _
  rw [norm_smul]
  calc
    _ ≤ ‖VerticalIntegral (modFivePerronIntegrand χ x) (1 + δ)‖ :=
      (mul_le_mul_of_nonneg_right modFive_perron_normalization (norm_nonneg _)).trans_eq
        (one_mul _)
    _ ≤ _ := hvert.trans (add_le_add hfin' le_rfl)

end TwoPointCorrelations

end OAI
