import OAI.Probability.SLE.Geometry.RoundedConnectorGeometry
import OAI.Probability.SLE.Geometry.RoundedConnectorBands

namespace OAI

/-! The connector changes horizontal position only at low height. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine

lemma lowConnector_normal_im_upper {H r X : ℝ} (hr : 1 < r) (hX : 2 * r < X)
    {z : ℂ} (hz : z.re ≤ connectorFourth H r X) (ha : |z.im| ≤ 1) :
    (normalRibbon (lowConnector H r X) (lowConnectorTangent H r X) z).im ≤ H + 2 * r + 1 := by
  have hr0 : 0 < r := by linarith
  obtain ⟨hc1, hc2, hc3⟩ := connector_cuts (H := H) hr0 hX
  by_cases h3 : z.re ≤ connectorThird H r X
  · by_cases h2 : z.re ≤ connectorSecond H r
    · by_cases h1 : z.re ≤ H
      · simp only [normalRibbon, lowConnector, lowConnectorTangent, curveJoin_of_le hz,
          curveJoin_of_le h3, curveJoin_of_le h2, curveJoin_of_le h1, connectorInitial,
          Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
        linarith
      · have ht : z.re - H ∈ Icc (0 : ℝ) (quarterLength r) := by
          constructor
          · linarith
          · dsimp only [connectorSecond] at h2
            linarith
        have hb := (quarterNormal_bounds hr ht ha).2.2.2
        simp only [normalRibbon, lowConnector, lowConnectorTangent, curveJoin_of_le hz,
          curveJoin_of_le h3, curveJoin_of_le h2, curveJoin_of_gt (lt_of_not_ge h1), connectorFirstTurn]
        rw [add_assoc]
        change ((H : ℂ) * Complex.I + quarterNormal r (z.re - H) z.im).im ≤ _
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
        linarith
    · simp only [normalRibbon, lowConnector, lowConnectorTangent, curveJoin_of_le hz,
        curveJoin_of_le h3, curveJoin_of_gt (lt_of_not_ge h2), connectorHorizontal,
        Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
      linarith [(abs_le.mp ha).2]
  · have ht : z.re - connectorThird H r X ∈ Icc (0 : ℝ) (quarterLength r) := by
      constructor
      · linarith
      · dsimp only [connectorFourth] at hz
        linarith
    have hb := (upperQuarterNormal_bounds hr ht ha).2.2.2
    simp only [normalRibbon, lowConnector, lowConnectorTangent, curveJoin_of_le hz,
      curveJoin_of_gt (lt_of_not_ge h3), connectorLastTurn]
    rw [add_assoc]
    change ((((X - r : ℝ) : ℂ) + ((H + r : ℝ) : ℂ) * Complex.I) +
      upperQuarterNormal r (z.re - connectorThird H r X) z.im).im ≤ _
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
    linarith

end SLEExactGauge.Serpentine

end

end OAI
