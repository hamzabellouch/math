import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowBounds

namespace OAI

/-! Bounded measurable finite interval sums and the squared two-window
inequality. These statements allow arbitrary complex coefficients. -/

namespace TwoPointCorrelations

open MeasureTheory Finset Set
open scoped Classical

lemma mrt_interval_sum_measurable {α : Type*} [MeasurableSpace α]
    (S : Finset ℕ) (a : ℕ → ℂ) {x h : α → ℝ}
    (hx : Measurable x) (hh : Measurable h) :
    Measurable (fun t => mrtIntervalSum S a (x t) (h t)) := by
  apply Finset.measurable_sum
  intro n _
  exact Measurable.ite
    ((measurableSet_lt hx measurable_const).inter
      (measurableSet_le measurable_const (hx.add hh)))
    measurable_const measurable_const

lemma mrt_interval_sum_norm (S : Finset ℕ) (a : ℕ → ℂ) (x h : ℝ) :
    ‖mrtIntervalSum S a x h‖ ≤ ∑ n ∈ S, ‖a n‖ := by
  unfold mrtIntervalSum
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n _
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using (norm_nonneg (a n))

lemma mrt_interval_sum_sq_integrableOn {α : Type*} [MeasurableSpace α]
    (S : Finset ℕ) (a : ℕ → ℂ) {μ : Measure α} {s : Set α}
    (hs : μ s ≠ ⊤) {x h : α → ℝ} (hx : Measurable x) (hh : Measurable h) :
    IntegrableOn (fun t => ‖mrtIntervalSum S a (x t) (h t)‖ ^ 2) s μ := by
  apply Measure.integrableOn_of_bounded hs
    (((mrt_interval_sum_measurable S a hx hh).norm.pow_const 2).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (mrt_interval_sum_norm S a (x t) (h t)) 2

lemma mrt_interval_sum_sq_intervalIntegrable (S : Finset ℕ) (a : ℕ → ℂ)
    {x h : ℝ → ℝ} (hx : Measurable x) (hh : Measurable h) (b c : ℝ) :
    IntervalIntegrable (fun t => ‖mrtIntervalSum S a (x t) (h t)‖ ^ 2)
      volume b c := by
  rw [intervalIntegrable_iff]
  apply mrt_interval_sum_sq_integrableOn S a _ hx hh
  exact measure_Ioc_lt_top.ne

lemma mrt_interval_sum_sq_split (S : Finset ℕ) (a : ℕ → ℂ) {x h w : ℝ}
    (hh : 0 ≤ h) (hw : h ≤ w) :
    ‖mrtIntervalSum S a x h‖ ^ 2 ≤
      2 * ‖mrtIntervalSum S a x w‖ ^ 2 +
        2 * ‖mrtIntervalSum S a (x + h) (w - h)‖ ^ 2 := by
  rw [← mrt_interval_sum_difference S a hh hw]
  have hn := norm_sub_le (mrtIntervalSum S a x w)
    (mrtIntervalSum S a (x + h) (w - h))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖mrtIntervalSum S a x w‖ -
    ‖mrtIntervalSum S a (x + h) (w - h)‖)]

theorem mrt_interval_sum_averaged_sq (S : Finset ℕ) (a : ℕ → ℂ)
    (x : ℝ) {h : ℝ} (hh : 0 < h) :
    ‖mrtIntervalSum S a x h‖ ^ 2 ≤ h⁻¹ *
      ((∫ w in h..3 * h, ‖mrtIntervalSum S a x w‖ ^ 2) +
        ∫ w in h..3 * h, ‖mrtIntervalSum S a (x + h) (w - h)‖ ^ 2) := by
  have hi₁ := mrt_interval_sum_sq_intervalIntegrable S a (x := fun _ => x) (h := id)
    measurable_const measurable_id h (3 * h)
  have hi₂ := mrt_interval_sum_sq_intervalIntegrable S a
    (x := fun _ => x+h) (h := fun w => w-h)
    measurable_const (measurable_id.sub measurable_const) h (3 * h)
  have hm := intervalIntegral.integral_mono_on (show h ≤ 3 * h by linarith)
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => ‖mrtIntervalSum S a x h‖ ^ 2) volume h (3 * h))
    ((hi₁.const_mul 2).add (hi₂.const_mul 2))
    (fun w hw => mrt_interval_sum_sq_split S a hh.le hw.1)
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hi₁.const_mul 2) (hi₂.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hm
  simp only [smul_eq_mul, id_eq] at hm
  apply (le_inv_mul_iff₀ hh).mpr
  nlinarith

end TwoPointCorrelations

end OAI
