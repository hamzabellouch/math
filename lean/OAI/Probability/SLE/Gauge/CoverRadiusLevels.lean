import OAI.Probability.SLE.Gauge.CoverSchedule
import OAI.Probability.SLE.Loewner.ActualRadiusStops

namespace OAI

/-! Absolute geometric radii are represented by nonnegative logarithmic
clock levels. The initial truncation disappears simultaneously throughout
every sufficiently late cover-test window. -/

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def coverLogLevel (z : ℂ) (T : ℝ) (j : ℕ) : ℝ :=
  max 0 (Real.log (2 * z.im) + T * (j : ℝ))

lemma coverLogLevel_nonneg (z : ℂ) (T : ℝ) (j : ℕ) : 0 ≤ coverLogLevel z T j :=
  le_max_left _ _

lemma coverLogLevel_monotone (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    Monotone (coverLogLevel z T) := by
  intro i j hij
  change max 0 (Real.log (2 * z.im) + T * (i : ℝ)) ≤
    max 0 (Real.log (2 * z.im) + T * (j : ℝ))
  apply max_le_max le_rfl
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith [mul_le_mul_of_nonneg_left hijR hT]

lemma eventually_cover_window_untruncated
    (z : ℂ) {T : ℝ} (hT : 0 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ coverTestWindow n,
      coverLogLevel z T j = Real.log (2 * z.im) + T * (j : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-Real.log (2 * z.im) / T)
  have hNT : -Real.log (2 * z.im) < T * (N : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hT).mp hN
  filter_upwards [eventually_ge_atTop (3 * N)] with n hn
  intro j hj
  have hjN : N ≤ j := by
    have hh := (Finset.mem_Icc.mp hj).1
    omega
  have hNj : T * (N : ℝ) ≤ T * (j : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hjN) hT.le
  exact max_eq_right (by linarith)

lemma radius_target_eq_coverRadius
    (z : ℂ) (hz : z ∈ upperHalfPlane) (T : ℝ) (j : ℕ)
    (hlevel : coverLogLevel z T j = Real.log (2 * z.im) + T * (j : ℝ)) :
    (2 * z.im) * Real.exp (-coverLogLevel z T j) = coverRadius T j := by
  have hr : 0 < 2 * z.im := mul_pos (by norm_num) hz
  rw [hlevel, neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hr]
  unfold coverRadius
  field_simp [(show 0 < z.im from hz).ne']

lemma eventually_cover_window_radius_target
    (z : ℂ) (hz : z ∈ upperHalfPlane) {T : ℝ} (hT : 0 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ coverTestWindow n,
      (2 * z.im) * Real.exp (-coverLogLevel z T j) = coverRadius T j := by
  filter_upwards [eventually_cover_window_untruncated z hT] with n hn
  exact fun j hj => radius_target_eq_coverRadius z hz T j (hn j hj)

end SLEExactGauge

end

end OAI
