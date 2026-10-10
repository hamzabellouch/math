import OAI.Probability.SLE.Gauge.SerpentineLayout

namespace OAI

/-! The displaced array and its vertical attachments avoid an explicit
upward shadow from the marked point. This gives the free upward route
used to control the conformal radius of every completed prefix. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

lemma center_horizontal_distance {s : ℝ} (hs : 0 ≤ s) (w : ℂ) :
    |(center s w).re - w.re| = s / 4 := by
  simp only [center, Complex.add_re, Complex.ofReal_re, add_sub_cancel_left, abs_mul]
  have hh : |displacementSign w| = 1 := by unfold displacementSign; split <;> norm_num
  rw [hh, one_mul, abs_of_nonneg (div_nonneg hs (by norm_num))]

lemma disk_horizontal_separation {s : ℝ} (hs : 0 < s) (w z : ℂ)
    (hz : z ∈ closedBall (center s w) (s / 20)) :
    s / 5 ≤ |z.re - w.re| := by
  have ha := abs_sub_le (center s w).re z.re w.re
  have hb : |(center s w).re - z.re| ≤ s / 20 := by
    have hn := Complex.abs_re_le_norm (center s w - z)
    have hd : ‖center s w - z‖ ≤ s / 20 := by
      rw [← dist_eq_norm, dist_comm]
      exact hz
    have hn' : |(center s w).re - z.re| ≤ ‖center s w - z‖ := by
      simpa only [Complex.sub_re] using hn
    exact hn'.trans hd
  rw [center_horizontal_distance hs.le w] at ha
  linarith

lemma column_avoids_upward_shadow {s : ℝ} (hs : 0 < s) (w : ℂ)
    {m j : ℕ} (hm : 0 < m) (hj : j ≤ 2 * m) {y a : ℝ}
    (hy : |y| ≤ halfHeight s) (ha : |a| ≤ 1) :
    ¬ (|((columnPoint (center s w) (halfHeight s) m j y a).re - w.re)| < s / 100 ∧
      w.im - s / 100 < (columnPoint (center s w) (halfHeight s) m j y a).im) := by
  have hh := disk_horizontal_separation hs w _ (column_inside_displaced_disk hs w hm hj hy ha)
  intro h
  linarith [h.1]

lemma turn_inside_displaced_disk {s : ℝ} (hs : 0 < s) (w : ℂ)
    {m j : ℕ} (hm : 0 < m) (hj : j + 1 ≤ 2 * m) (t : ℝ) {a : ℝ} (ha : |a| ≤ 1) :
    turnPoint (center s w) (halfHeight s) m j t a ∈ closedBall (center s w) (s / 20) := by
  have hh : 0 < halfHeight s := by unfold halfHeight; positivity
  have hb := turnPoint_bound hh hm hj (center s w) t ha
  change dist _ _ ≤ s / 20
  dsimp only [halfHeight] at hb ⊢
  linarith

lemma turn_avoids_upward_shadow {s : ℝ} (hs : 0 < s) (w : ℂ)
    {m j : ℕ} (hm : 0 < m) (hj : j + 1 ≤ 2 * m) (t : ℝ) {a : ℝ} (ha : |a| ≤ 1) :
    ¬ (|(turnPoint (center s w) (halfHeight s) m j t a).re - w.re| < s / 100 ∧
      w.im - s / 100 < (turnPoint (center s w) (halfHeight s) m j t a).im) := by
  have hh := disk_horizontal_separation hs w _ (turn_inside_displaced_disk hs w hm hj t ha)
  intro h
  linarith [h.1]

/-- The low part of the connector lies below the shadow. -/
lemma low_connector_avoids_upward_shadow {s : ℝ} (hs : 0 < s) (w z : ℂ)
    (hw : s ≤ w.im) (hz : z.im ≤ s / 2) :
    ¬ (|z.re - w.re| < s / 100 ∧ w.im - s / 100 < z.im) := by
  intro h
  linarith [h.2]

/-- The vertical attachment over either outer column stays horizontally
separated, regardless of its height. -/
lemma attachment_avoids_upward_shadow {s : ℝ} (hs : 0 < s) (w z : ℂ)
    {x : ℝ} (hx : |x| ≤ halfHeight s)
    (hz : |z.re - ((center s w).re + x)| ≤ s / 1000) :
    ¬ (|z.re - w.re| < s / 100 ∧ w.im - s / 100 < z.im) := by
  have h1 := abs_sub_le (center s w).re (((center s w).re + x)) w.re
  have h2 := abs_sub_le (((center s w).re + x)) z.re w.re
  have hxx : |(center s w).re - ((center s w).re + x)| = |x| := by
    rw [sub_add_eq_sub_sub, sub_self, zero_sub, abs_neg]
  rw [center_horizontal_distance hs.le w, hxx] at h1
  rw [abs_sub_comm (((center s w).re + x)) z.re] at h2
  dsimp only [halfHeight] at hx
  intro h
  linarith [h.1]

end SLEExactGauge.Serpentine

end

end OAI
