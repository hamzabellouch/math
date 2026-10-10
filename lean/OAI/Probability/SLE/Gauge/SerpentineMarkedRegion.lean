import OAI.Probability.SLE.Gauge.SerpentineFittedShadow

namespace OAI

/-! The connector lies below the marked point, and every later part of
the rightward serpentine lies strictly to its right. This is the geometric
separation used to append the marked-point access hook. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

theorem physicalFitChart_low_or_right {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) {z : ℂ} (ha : |z.im| ≤ 1) :
    (physicalFitChart s w m z).im ≤ s / 2 ∨
      |w.re| + s / 5 ≤ (physicalFitChart s w m z).re := by
  by_cases h4 : z.re ≤ connectorFourth (fitHeight m) (fitRadius m) (fitX s w m)
  · exact Or.inl (physicalFitChart_low hs w hw hm ha h4)
  · right
    by_cases hA : z.re ≤ connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)
    · have hh := physicalFitChart_tail_right hs w hw hm ha (lt_of_not_ge h4) hA
      linarith
    · have hh := physicalFitChart_array_right hs w hm ha (lt_of_not_ge hA)
      linarith

theorem physicalFitChart_marked_distance {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    (hwr : 0 ≤ w.re) {m : ℕ} (hm : 0 < m) {z : ℂ} (ha : |z.im| ≤ 1) :
    s / 5 ≤ dist (physicalFitChart s w m z) w := by
  rw [dist_eq_norm]
  rcases physicalFitChart_low_or_right hs w hw hm ha with hlow | hright
  · have hh := Complex.abs_im_le_norm (physicalFitChart s w m z - w)
    rw [Complex.sub_im] at hh
    have hl := neg_le_abs ((physicalFitChart s w m z).im - w.im)
    linarith
  · rw [abs_of_nonneg hwr] at hright
    have hh := Complex.abs_re_le_norm (physicalFitChart s w m z - w)
    rw [Complex.sub_re] at hh
    have hl := le_abs_self ((physicalFitChart s w m z).re - w.re)
    linarith

theorem physicalFitChart_hook_region {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    (hwr : 0 ≤ w.re) {m : ℕ} (hm : 0 < m) {z : ℂ} (ha : |z.im| ≤ 1) :
    (physicalFitChart s w m z).im < w.im ∨ w.re < (physicalFitChart s w m z).re := by
  rcases physicalFitChart_low_or_right hs w hw hm ha with hh | hh
  · left
    linarith
  · right
    rw [abs_of_nonneg hwr] at hh
    linarith

end SLEExactGauge.Serpentine

end

end OAI
