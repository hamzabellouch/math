import OAI.Probability.SLE.Gauge.SerpentineCompleteEmbedding

namespace OAI

/-! The complete normal ribbon starts on the real boundary and every
positive longitudinal coordinate lies in the upper half-plane. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

lemma lowConnector_normal_im_pos {H r X : ℝ} (hH : 1 < H) (hr : 1 < r) (hX : 2 * r < X)
    {z : ℂ} (hz : 0 < z.re) (ha : |z.im| ≤ 1) :
    0 < (normalRibbon (lowConnector H r X) (lowConnectorTangent H r X) z).im := by
  have hr0 : 0 < r := by linarith
  obtain ⟨hc1, hc2, hc3⟩ := connector_cuts (H := H) hr0 hX
  by_cases h4 : z.re ≤ connectorFourth H r X
  · by_cases h3 : z.re ≤ connectorThird H r X
    · by_cases h2 : z.re ≤ connectorSecond H r
      · by_cases h1 : z.re ≤ H
        · simp only [normalRibbon, lowConnector, lowConnectorTangent, curveJoin_of_le h4,
            curveJoin_of_le h3, curveJoin_of_le h2, curveJoin_of_le h1, connectorInitial,
            Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
          exact hz
        · have ht : z.re - H ∈ Icc (0 : ℝ) (quarterLength r) := by
            constructor
            · linarith
            · dsimp only [connectorSecond] at h2
              linarith
          have hb := (quarterNormal_bounds hr ht ha).2.2.1
          simp only [normalRibbon, lowConnector, lowConnectorTangent, curveJoin_of_le h4,
            curveJoin_of_le h3, curveJoin_of_le h2, curveJoin_of_gt (lt_of_not_ge h1), connectorFirstTurn]
          rw [add_assoc]
          change 0 < ((H : ℂ) * Complex.I + quarterNormal r (z.re - H) z.im).im
          simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
          linarith
      · simp only [normalRibbon, lowConnector, lowConnectorTangent, curveJoin_of_le h4,
          curveJoin_of_le h3, curveJoin_of_gt (lt_of_not_ge h2), connectorHorizontal,
          Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
        linarith [(abs_le.mp ha).1]
    · have ht : z.re - connectorThird H r X ∈ Icc (0 : ℝ) (quarterLength r) := by
        constructor
        · linarith
        · dsimp only [connectorFourth] at h4
          linarith
      have hb := (upperQuarterNormal_bounds hr ht ha).2.2.1
      simp only [normalRibbon, lowConnector, lowConnectorTangent, curveJoin_of_le h4,
        curveJoin_of_gt (lt_of_not_ge h3), connectorLastTurn]
      rw [add_assoc]
      change 0 < ((((X - r : ℝ) : ℂ) + ((H + r : ℝ) : ℂ) * Complex.I) +
        upperQuarterNormal r (z.re - connectorThird H r X) z.im).im
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
      linarith
  · simp only [normalRibbon, lowConnector, lowConnectorTangent, curveJoin_of_gt (lt_of_not_ge h4),
      connectorTail, Complex.add_im, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_add]
    linarith

/-- The actual entire ribbon lies above the real boundary at every
positive longitudinal parameter. -/
theorem complete_normal_upper {m : ℕ} (hm : 0 < m) {H r X Y : ℝ}
    (hH : 1 < H) (hr : 1 < r) (hX : 2 * r < X) (hY : 300 * (m : ℝ) < Y)
    {z : ℂ} (hz : 0 < z.re) (ha : |z.im| ≤ 1) :
    0 < (normalRibbon (completeSpine m H r X Y) (completeTangent m H r X Y) z).im := by
  by_cases hA : z.re ≤ connectorEntry H r X Y
  · rw [complete_normal_of_le m H r X Y hA]
    exact lowConnector_normal_im_pos hH hr hX hz ha
  · have hz' : 0 ≤ (z - (connectorEntry H r X Y : ℂ)).re ∧
        |(z - (connectorEntry H r X Y : ℂ)).im| ≤ 1 := by
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      exact ⟨by linarith, ha⟩
    have hb := array_normal_im_lower hm hz'
    rw [complete_normal_of_gt m H r X Y (lt_of_not_ge hA)]
    simp only [arrayCenter, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
    linarith

end SLEExactGauge.Serpentine

end

end OAI
