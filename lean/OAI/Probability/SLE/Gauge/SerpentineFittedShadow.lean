import OAI.Probability.SLE.Gauge.SerpentineFittedRegion

namespace OAI

/-! The complete fitted ribbon avoids a fixed upward shadow of the
marked point, including the connector and the infinite final tail. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

lemma fit_width_le {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 0 < m) :
    ribbonWidth (halfHeight s) m ≤ s / 20000 := by
  have hmul := fit_width_mul hs hm
  have hp := (fit_width_pos hs hm).le
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

lemma fit_scaledX {s : ℝ} (hs : 0 < s) (w : ℂ) {m : ℕ} (hm : 0 < m) :
    ribbonWidth (halfHeight s) m * fitX s w m = |w.re| + s / 4 - s / 200 := by
  unfold fitX halfHeight
  exact mul_div_cancel₀ _ (fit_width_pos hs hm).ne'

lemma physicalFitChart_low {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) {z : ℂ} (ha : |z.im| ≤ 1)
    (hz : z.re ≤ connectorFourth (fitHeight m) (fitRadius m) (fitX s w m)) :
    (physicalFitChart s w m z).im ≤ s / 2 := by
  obtain ⟨hr, hx, hy, _⟩ := fit_parameters hs w hw hm
  have hA : z.re ≤ connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m) := by
    have hY : fitHeight m + 2 * fitRadius m < fitY s w m := by
      linarith [Nat.cast_nonneg (α := ℝ) m]
    unfold connectorEntry
    linarith
  have hlow := lowConnector_normal_im_upper (by linarith : 1 < fitRadius m) hx hz ha
  have hℓ := (fit_width_pos hs hm).le
  have hmul := fit_width_mul hs hm
  have hle := fit_width_le hs hm
  have hscaled := mul_le_mul_of_nonneg_left hlow hℓ
  change ((ribbonWidth (halfHeight s) m : ℂ) *
    normalRibbon (completeSpine m _ _ _ _) (completeTangent m _ _ _ _) z).im ≤ _
  rw [complete_normal_of_le m _ _ _ _ hA]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  dsimp only [fitHeight, fitRadius] at hscaled ⊢
  nlinarith

lemma physicalFitChart_tail_right {s : ℝ} (hs : 0 < s) (w : ℂ) (_hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) {z : ℂ} (ha : |z.im| ≤ 1)
    (hz : connectorFourth (fitHeight m) (fitRadius m) (fitX s w m) < z.re)
    (hA : z.re ≤ connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)) :
    s / 5 ≤ (physicalFitChart s w m z).re - |w.re| := by
  have hℓ := (fit_width_pos hs hm).le
  have hx := fit_scaledX hs w hm
  have hle := fit_width_le hs hm
  have hza := mul_le_mul_of_nonneg_left (abs_le.mp ha).2 hℓ
  change ((ribbonWidth (halfHeight s) m : ℂ) *
    normalRibbon (completeSpine m _ _ _ _) (completeTangent m _ _ _ _) z).re - _ ≥ _
  rw [complete_normal_of_le m _ _ _ _ hA, normalRibbon,
    (lowConnector_after hz).1, (lowConnector_after hz).2]
  simp only [connectorTail, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add]
  nlinarith

lemma physicalFitChart_array_right {s : ℝ} (hs : 0 < s) (w : ℂ)
    {m : ℕ} (hm : 0 < m) {z : ℂ} (ha : |z.im| ≤ 1)
    (hA : connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m) < z.re) :
    s / 5 ≤ (physicalFitChart s w m z).re - |w.re| := by
  have hℓ := (fit_width_pos hs hm).le
  have hmul := fit_width_mul hs hm
  let A := connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)
  have hz' : 0 ≤ (z - (A : ℂ)).re ∧ |(z - (A : ℂ)).im| ≤ 1 := by
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    exact ⟨by dsimp [A]; linarith, ha⟩
  have hbound := mul_le_mul_of_nonneg_left (array_normal_re_lower hm hz') hℓ
  have hcenter := congrArg Complex.re (fit_scaled_arrayCenter hs w hm)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    positiveCenter, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero] at hcenter
  change ((ribbonWidth (halfHeight s) m : ℂ) *
    normalRibbon (completeSpine m _ _ _ _) (completeTangent m _ _ _ _) z).re - _ ≥ _
  rw [complete_normal_of_gt m _ _ _ _ hA]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re]
  dsimp [A] at hbound
  nlinarith

theorem physicalFitChart_avoids_shadow {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    {m : ℕ} (hm : 0 < m) {z : ℂ} (ha : |z.im| ≤ 1) :
    ¬ (abs ((physicalFitChart s w m z).re - |w.re|) < s / 100 ∧
      w.im - s / 100 < (physicalFitChart s w m z).im) := by
  intro h
  by_cases h4 : z.re ≤ connectorFourth (fitHeight m) (fitRadius m) (fitX s w m)
  · have hh := physicalFitChart_low hs w hw hm ha h4
    linarith [h.2]
  · by_cases hA : z.re ≤ connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)
    · have hh := physicalFitChart_tail_right hs w hw hm ha (lt_of_not_ge h4) hA
      have hl := le_abs_self ((physicalFitChart s w m z).re - |w.re|)
      linarith [h.1]
    · have hh := physicalFitChart_array_right hs w hm ha (lt_of_not_ge hA)
      have hl := le_abs_self ((physicalFitChart s w m z).re - |w.re|)
      linarith [h.1]

end SLEExactGauge.Serpentine

end

end OAI
