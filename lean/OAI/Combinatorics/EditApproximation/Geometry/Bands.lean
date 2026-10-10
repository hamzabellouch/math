import Mathlib

namespace OAI

/-!
# Predicted-band geometry

The prefix-cost predictor is 1-Lipschitz, while its velocity has a strict
margin below one. This gives narrow bands without a convexity assumption
on the set of allowed endpoints (Sections 5 and 6 of the manuscript).
-/

namespace EditApproximation

def inPredictedBand (prefixCost : ℝ → ℝ) (origin velocity margin width point : ℝ) : Prop :=
  |point - origin - velocity * prefixCost point| ≤ margin * width

theorem predicted_band_diameter {prefixCost : ℝ → ℝ}
    {origin velocity margin width p q : ℝ}
    (hmargin : 0 < margin) (hvelocity : |velocity| ≤ 1 - margin)
    (hLipschitz : |prefixCost p - prefixCost q| ≤ |p - q|)
    (hp : inPredictedBand prefixCost origin velocity margin width p)
    (hq : inPredictedBand prefixCost origin velocity margin width q) :
    |p - q| ≤ 2 * width := by
  have hid : p - q =
      (p - origin - velocity * prefixCost p) - (q - origin - velocity * prefixCost q) +
        velocity * (prefixCost p - prefixCost q) := by ring
  have htri := (abs_add_le
    ((p - origin - velocity * prefixCost p) - (q - origin - velocity * prefixCost q))
    (velocity * (prefixCost p - prefixCost q))).trans
      (add_le_add (abs_sub _ _) le_rfl)
  rw [← hid, abs_mul] at htri
  have hprod := mul_le_mul hvelocity hLipschitz (abs_nonneg _)
    ((abs_nonneg velocity).trans hvelocity)
  change |p - origin - velocity * prefixCost p| ≤ margin * width at hp
  change |q - origin - velocity * prefixCost q| ≤ margin * width at hq
  have hscaled : margin * |p - q| ≤ margin * (2 * width) := by nlinarith
  exact le_of_mul_le_mul_left hscaled hmargin

/-- The comparison prefix error is the weighted deviation plus two
warmup-mass discrepancy charges. -/
theorem comparison_prefix_prediction_error
    {point origin velocity predictedVelocity prefixMass prefixCost totalMass discrepancy deviation : ℝ}
    (hprefix : 0 ≤ prefixMass) (hprefixTotal : prefixMass ≤ totalMass)
    (hprediction : |velocity - predictedVelocity| * totalMass ≤ discrepancy)
    (hvelocity : |predictedVelocity| ≤ 1)
    (hcostLower : prefixMass - discrepancy ≤ prefixCost)
    (hcostUpper : prefixCost ≤ prefixMass)
    (hdeviation : |point - origin - velocity * prefixMass| ≤ deviation) :
    |point - origin - predictedVelocity * prefixCost| ≤ deviation + 2 * discrepancy := by
  have hcostDiff : |prefixMass - prefixCost| ≤ discrepancy := by
    rw [abs_of_nonneg (by linarith : 0 ≤ prefixMass - prefixCost)]
    linarith
  have hfirst : |(velocity - predictedVelocity) * prefixMass| ≤ discrepancy := by
    rw [abs_mul, abs_of_nonneg hprefix]
    exact (mul_le_mul_of_nonneg_left hprefixTotal (abs_nonneg _)).trans hprediction
  have hsecond : |predictedVelocity * (prefixMass - prefixCost)| ≤ discrepancy := by
    rw [abs_mul]
    have hprod := mul_le_mul hvelocity hcostDiff (abs_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hprod
  have hid : point - origin - predictedVelocity * prefixCost =
      (point - origin - velocity * prefixMass) +
        (velocity - predictedVelocity) * prefixMass +
          predictedVelocity * (prefixMass - prefixCost) := by ring
  rw [hid]
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (by linarith)

end EditApproximation

end OAI
