import OAI.Probability.SLE.Gauge.SerpentineFittedChart
import OAI.Probability.SLE.Gauge.SerpentineArrayRegion

namespace OAI

/-! The retained integer strips lie in the prescribed displaced disk
after multiplication by the physical width. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

def physicalFitChart (s : ℝ) (w : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  (ribbonWidth (halfHeight s) m : ℂ) * fitChart s w m z

lemma fitChart_retained_distance {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m j i : ℕ} (hm : 0 < m) (hj : j < m) (hi : i < m) {z : ℂ}
    (hz : z.re ∈ Icc
      ((retainedStep (connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) m j i : ℝ) + 1 / 3)
      ((retainedStep (connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) m j i : ℝ) + 2 / 3))
    (ha : |z.im| ≤ 1) :
    dist (fitChart s w m z) (arrayCenter m (fitX s w m) (fitY s w m)) ≤ 300 * m := by
  have hA : 0 ≤ connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m) :=
    (by unfold fitHeight; positivity : (0 : ℝ) ≤ fitHeight m).trans (fit_entry_lower hs w hw hm)
  have hmid := retained_middle_in_straight hA hi hz
  have he : columnEntry (connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) m j =
      connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m) + columnEntry 0 m j := by
    unfold columnEntry
    ring
  rw [he] at hmid
  have hu : z.re - connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m) -
      columnEntry 0 m j ∈ Icc (0 : ℝ) (200 * m) := ⟨by linarith [hmid.1], by linarith [hmid.2]⟩
  unfold fitChart fitSpine fitTangent
  rw [retained_strip_on_column hm hj hi _ _ _ _ hA hz, dist_self_add_left]
  have hb := columnPoint_bound (j := j) (by positivity : (0 : ℝ) < 100 * m) hm (by omega) 0
      (straight_height_bound m j hu) ha
  rw [dist_zero_right] at hb
  linarith

lemma physicalFitChart_retained_distance {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m j i : ℕ} (hm : 0 < m) (hj : j < m) (hi : i < m) {z : ℂ}
    (hz : z.re ∈ Icc
      ((retainedStep (connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) m j i : ℝ) + 1 / 3)
      ((retainedStep (connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) m j i : ℝ) + 2 / 3))
    (ha : |z.im| ≤ 1) :
    dist (physicalFitChart s w m z) (positiveCenter s w) ≤ 3 * s / 200 := by
  have hd := fitChart_retained_distance hs w hw hm hj hi hz ha
  have hℓ := fit_width_pos hs hm
  have hmul := fit_width_mul hs hm
  rw [physicalFitChart, ← fit_scaled_arrayCenter hs w hm, dist_eq_norm, ← mul_sub, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ]
  have h := mul_le_mul_of_nonneg_left hd hℓ.le
  rw [dist_eq_norm] at h
  nlinarith

lemma positiveCenter_eq_center {s : ℝ} {w : ℂ} (hw : 0 ≤ w.re) :
    positiveCenter s w = center s w := by
  apply Complex.ext <;>
    simp [positiveCenter, center, displacementSign, hw, abs_of_nonneg hw]

lemma physicalFitChart_retained_disk {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    (hwr : 0 ≤ w.re) {m j i : ℕ} (hm : 0 < m) (hj : j < m) (hi : i < m) {z : ℂ}
    (hz : z.re ∈ Icc
      ((retainedStep (connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) m j i : ℝ) + 1 / 3)
      ((retainedStep (connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) m j i : ℝ) + 2 / 3))
    (ha : |z.im| ≤ 1) :
    physicalFitChart s w m z ∈ closedBall (center s w) (s / 20) := by
  have hd := physicalFitChart_retained_distance hs w hw hm hj hi hz ha
  rw [positiveCenter_eq_center hwr] at hd
  change dist _ _ ≤ _
  linarith

end SLEExactGauge.Serpentine

end

end OAI
