import OAI.Probability.SLE.Gauge.SerpentineHorizontalBound

namespace OAI

/-! The physical experiment lies strictly between two fixed exterior
vertical lines. These lines provide unobstructed real-boundary exits. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

lemma physicalFitChart_re_bounds {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (w : ℂ) (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) {m : ℕ} (hm : 0 < m)
    {z : ℂ} (hz : z ∈ closedRibbon) :
    -2 ≤ (physicalFitChart s w m z).re ∧ (physicalFitChart s w m z).re ≤ 2 := by
  obtain ⟨hr, hx, _, _⟩ := fit_parameters hs w hw hm
  have hH : 0 ≤ fitHeight m := by unfold fitHeight; positivity
  have hℓ := (fit_width_pos hs hm).le
  have hℓ1 := fit_width_le hs hm
  have hX := fit_scaledX hs w hm
  have hwr := (Complex.abs_re_le_norm w).trans hw1
  let A := connectorEntry (fitHeight m) (fitRadius m) (fitX s w m) (fitY s w m)
  by_cases hA : z.re ≤ A
  · have hb := lowConnector_normal_re_bounds hH (by linarith : 0 < fitRadius m) hx hz
    have hlo := mul_le_mul_of_nonneg_left hb.1 hℓ
    have hhi := mul_le_mul_of_nonneg_left hb.2 hℓ
    change -2 ≤ ((ribbonWidth (halfHeight s) m : ℂ) *
      normalRibbon (completeSpine m _ _ _ _) (completeTangent m _ _ _ _) z).re ∧
      ((ribbonWidth (halfHeight s) m : ℂ) *
      normalRibbon (completeSpine m _ _ _ _) (completeTangent m _ _ _ _) z).re ≤ 2
    rw [complete_normal_of_le m _ _ _ _ hA]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    constructor <;> nlinarith
  · have hz' : 0 ≤ (z - (A : ℂ)).re ∧ |(z - (A : ℂ)).im| ≤ 1 := by
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      exact ⟨by linarith, hz.2⟩
    have hlo := mul_le_mul_of_nonneg_left (array_normal_re_lower hm hz') hℓ
    have hhi := mul_le_mul_of_nonneg_left (array_normal_re_upper hm hz') hℓ
    have hcenter := congrArg Complex.re (fit_scaled_arrayCenter hs w hm)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      positiveCenter, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, add_zero] at hcenter
    have hmℓ := fit_width_mul hs hm
    change -2 ≤ ((ribbonWidth (halfHeight s) m : ℂ) *
      normalRibbon (completeSpine m _ _ _ _) (completeTangent m _ _ _ _) z).re ∧
      ((ribbonWidth (halfHeight s) m : ℂ) *
      normalRibbon (completeSpine m _ _ _ _) (completeTangent m _ _ _ _) z).re ≤ 2
    rw [complete_normal_of_gt m _ _ _ _ (lt_of_not_ge hA)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.add_re]
    dsimp only [A] at hlo hhi
    constructor <;> nlinarith [abs_nonneg w.re]

end SLEExactGauge.Serpentine

end

end OAI
