import OAI.NumberTheory.TwoPointCorrelations.HalaszPerronWindowKernel
import OAI.NumberTheory.TwoPointCorrelations.HalaszUnsmoothing
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace OAI

/-! Exact inversion for the narrow Perron window. Absolute convergence on
the line is enough, including the smooth Euler series at real part one. -/

namespace TwoPointCorrelations

open Complex MeasureTheory Erdos970 Finset

lemma halasz_LSeries_line_continuous (a : ℕ → ℂ) (ha : LSeriesSummable a 1) :
    Continuous (fun t : ℝ => LSeries a (1 + (t : ℂ) * I)) := by
  change Continuous (fun t : ℝ => ∑' n, LSeries.term a (1 + (t : ℂ) * I) n)
  refine continuous_tsum (u := fun n => ‖LSeries.term a 1 n‖) ?_ ha.norm ?_
  · intro n
    by_cases hn : n = 0
    · subst n
      simp only [LSeries.term_zero]
      exact continuous_const
    · simp_rw [LSeries.term_of_ne_zero hn]
      apply continuous_const.div
      · exact (show Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I) by
          fun_prop).const_cpow (Or.inl (by exact_mod_cast hn))
      · intro t
        exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
  · intro n t
    simp [LSeries.norm_term_eq]

lemma halasz_LSeries_line_bound (a : ℕ → ℂ) (ha : LSeriesSummable a 1) (t : ℝ) :
    ‖LSeries a (1 + (t : ℂ) * I)‖ ≤ ∑' n, ‖LSeries.term a 1 n‖ := by
  apply tsum_of_norm_bounded ha.norm.hasSum
  intro n
  simp [LSeries.norm_term_eq]

lemma halasz_LSeries_perron_integrable (a : ℕ → ℂ) (ha : LSeriesSummable a 1)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => LSeries a (1 + (t : ℂ) * I) *
      modFivePerronKernel x (1 + (t : ℂ) * I)) := by
  have hk := modFivePerronKernel_integrable hx (by norm_num : (1 / 2 : ℝ) ≤ 1)
  simp only [Complex.ofReal_one] at hk
  apply (hk.norm.const_mul (∑' n, ‖LSeries.term a 1 n‖)).mono'
    ((halasz_LSeries_line_continuous a ha).aestronglyMeasurable.mul hk.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  simp only [Pi.mul_apply]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (halasz_LSeries_line_bound a ha t) (norm_nonneg _)

lemma halasz_LSeries_window_integrable (a : ℕ → ℂ) (ha : LSeriesSummable a 1)
    {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    Integrable (fun t : ℝ => LSeries a (1 + (t : ℂ) * I) *
      halaszPerronWindowKernel x δ (1 + (t : ℂ) * I)) := by
  have hy : 0 < (1 + δ) * x := mul_pos (by linarith) hx
  have hi := (((halasz_LSeries_perron_integrable a ha hy).const_mul
    ((1 + δ : ℝ) : ℂ)).sub (halasz_LSeries_perron_integrable a ha hx)).div_const (δ : ℂ)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro t
  simp only [Pi.sub_apply]
  unfold halaszPerronWindowKernel
  ring

theorem halasz_window_perron (a : ℕ → ℂ) (ha : LSeriesSummable a 1)
    {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hxnat : ∀ n : ℕ, x ≠ (n : ℝ))
    (hynat : ∀ n : ℕ, (1 + δ) * x ≠ (n : ℝ)) :
    VerticalIntegral' (fun s => LSeries a s * halaszPerronWindowKernel x δ s) 1 =
      (((1 + δ : ℝ) : ℂ) * halaszTriangularSum a ((1 + δ) * x) -
        halaszTriangularSum a x) / (δ : ℂ) := by
  have hy : 0 < (1 + δ) * x := mul_pos (by linarith) hx
  have hxI := halasz_LSeries_perron_integrable a ha hx
  have hyI := halasz_LSeries_perron_integrable a ha hy
  have hxP := modFivePerron_finite_sum a hx (by norm_num : (1 / 2 : ℝ) ≤ 1) ha hxnat
  have hyP := modFivePerron_finite_sum a hy (by norm_num : (1 / 2 : ℝ) ≤ 1) ha hynat
  change _ = (((1 + δ : ℝ) : ℂ) * _ - _) / (δ : ℂ)
  rw [halaszTriangularSum, halaszTriangularSum, ← hxP, ← hyP]
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul, Complex.ofReal_one]
  have he (t : ℝ) : LSeries a (1 + (t : ℂ) * I) *
      halaszPerronWindowKernel x δ (1 + (t : ℂ) * I) =
      (((1 + δ : ℝ) : ℂ) * (LSeries a (1 + (t : ℂ) * I) *
        modFivePerronKernel ((1 + δ) * x) (1 + (t : ℂ) * I)) -
        LSeries a (1 + (t : ℂ) * I) * modFivePerronKernel x (1 + (t : ℂ) * I)) /
          (δ : ℂ) := by unfold halaszPerronWindowKernel; ring
  simp_rw [he]
  rw [integral_div, integral_sub (hyI.const_mul _) hxI, integral_const_mul]
  ring

theorem halasz_window_unsmoothing (a : ℕ → ℂ) (ha : LSeriesSummable a 1)
    {x B : ℝ} (hx : 0 < x) (m : ℕ) (hm : 0 < m)
    (hxnat : ∀ n : ℕ, x ≠ (n : ℝ))
    (hB : ∀ n ∈ Icc (⌊x⌋₊ + 1) (⌊x⌋₊ + m), ‖a n‖ ≤ B) :
    ‖VerticalIntegral' (fun s => LSeries a s * halaszPerronWindowKernel x (m / x) s) 1 -
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n‖ ≤ B * m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (1 + (m : ℝ) / x) * x = x + m := by field_simp
  have hynat (n : ℕ) : (1 + (m : ℝ) / x) * x ≠ (n : ℝ) := by
    rw [he]
    intro h
    by_cases hmn : m ≤ n
    · apply hxnat (n - m)
      rw [Nat.cast_sub hmn]
      linarith
    · have hnm : (n : ℝ) < m := by exact_mod_cast (Nat.lt_of_not_ge hmn)
      linarith
  rw [halasz_window_perron a ha hx (div_pos hmR hx) hxnat hynat, he]
  have hscale : (((1 + (m : ℝ) / x : ℝ) : ℂ) * halaszTriangularSum a (x + m) -
      halaszTriangularSum a x) / ((m : ℝ) / x : ℝ) =
      (((x + m : ℝ) : ℂ) * halaszTriangularSum a (x + m) -
        (x : ℂ) * halaszTriangularSum a x) / (m : ℂ) := by
    push_cast
    field_simp [hx.ne', Nat.ne_of_gt hm]
  rw [hscale]
  exact halasz_unsmoothing_error a hx m hm hB

end TwoPointCorrelations

end OAI
