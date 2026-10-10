import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquare

namespace OAI

/-! The exact two-window identity used to remove the moving additive
endpoint before the logarithmic Fourier estimate. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtIntervalSum (S : Finset ℕ) (a : ℕ → ℂ) (x h : ℝ) : ℂ :=
  ∑ n ∈ S, if x < (n : ℝ) ∧ (n : ℝ) ≤ x + h then a n else 0

lemma mrt_interval_sum_split (S : Finset ℕ) (a : ℕ → ℂ) {x h w : ℝ}
    (hh : 0 ≤ h) (hw : h ≤ w) :
    mrtIntervalSum S a x w =
      mrtIntervalSum S a x h + mrtIntervalSum S a (x + h) (w - h) := by
  unfold mrtIntervalSum
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  have he : x + h + (w - h) = x + w := by ring
  rw [he]
  by_cases hx : x < (n : ℝ)
  · by_cases hh' : (n : ℝ) ≤ x + h
    · have hw' : (n : ℝ) ≤ x + w := hh'.trans (by linarith)
      have hn : ¬x + h < (n : ℝ) := not_lt.mpr hh'
      simp [hx, hh', hw', hn]
    · have hn : x + h < (n : ℝ) := lt_of_not_ge hh'
      simp [hx, hh', hn]
  · have hn : ¬x + h < (n : ℝ) := by intro hn; exact hx (by linarith)
    simp [hx, hn]

lemma mrt_interval_sum_difference (S : Finset ℕ) (a : ℕ → ℂ) {x h w : ℝ}
    (hh : 0 ≤ h) (hw : h ≤ w) :
    mrtIntervalSum S a x w - mrtIntervalSum S a (x + h) (w - h) =
      mrtIntervalSum S a x h := by
  rw [mrt_interval_sum_split S a hh hw]
  abel

theorem mrt_interval_sum_average_difference (S : Finset ℕ) (a : ℕ → ℂ)
    (x : ℝ) {h : ℝ} (hh : 0 < h) :
    (1 / (2 * h) : ℂ) *
        (∫ w in h..3 * h,
          mrtIntervalSum S a x w - mrtIntervalSum S a (x + h) (w - h)) =
      mrtIntervalSum S a x h := by
  have hi : (∫ w in h..3 * h,
      mrtIntervalSum S a x w - mrtIntervalSum S a (x + h) (w - h)) =
      (∫ _w in h..3 * h, mrtIntervalSum S a x h) := by
    apply intervalIntegral.integral_congr
    intro w hw
    have hhw : h ≤ w := by
      rw [Set.uIcc_of_le (show h ≤ 3 * h by linarith)] at hw
      exact hw.1
    exact mrt_interval_sum_difference S a hh.le hhw
  rw [hi, intervalIntegral.integral_const]
  have hn : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  field_simp
  rw [Complex.real_smul]
  push_cast
  ring

end TwoPointCorrelations

end OAI
