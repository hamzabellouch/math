import OAI.Combinatorics.EditApproximation.Refinement.StageWarmup
import OAI.Combinatorics.EditApproximation.Numerics.RationalPruning

namespace OAI

/-! Good-seed equality with the finite local scale and center rule. -/

namespace EditApproximation

theorem refinement_cone_locality_numeric {w wr distance b a F cone : ℚ}
    (hw : 0 < w) (ha : 1 ≤ a) (hF : 1 ≤ F) (hdistance : 0 ≤ distance)
    (hspatial : |w - wr| ≤ 32 * F * distance)
    (heligible : b / (4 * a) ≤ wr ∧ wr ≤ 8 * F * b)
    (hconeLower : 128 * F * distance ≤ cone) (hconeUpper : cone ≤ w) :
    w / (16 * F) ≤ b ∧ b ≤ 8 * a * w ∧ distance ≤ w := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hF0 : 0 < F := lt_of_lt_of_le zero_lt_one hF
  have hnear : 32 * F * distance ≤ w / 4 := by nlinarith only [hconeLower, hconeUpper]
  have hdiff := abs_le.mp hspatial
  have hwrLower : 3 * w / 4 ≤ wr := by linarith only [hdiff.2, hnear]
  have hwrUpper : wr ≤ 5 * w / 4 := by linarith only [hdiff.1, hnear]
  have hlower : w / (16 * F) ≤ b := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * F)).2
    nlinarith only [hwrLower, heligible.2, hw.le]
  have hb : b ≤ wr * (4 * a) := (div_le_iff₀ (by positivity : 0 < 4 * a)).1 heligible.1
  have hmul := mul_le_mul_of_nonneg_right hwrUpper (show 0 ≤ 4 * a by positivity)
  have hupper : b ≤ 8 * a * w := by nlinarith only [hb, hmul, mul_nonneg ha0.le hw.le]
  have hdist : distance ≤ 128 * F * distance := by
    have hm := mul_le_mul_of_nonneg_right hF hdistance
    nlinarith only [hm, hdistance]
  exact ⟨hlower, hupper, hdist.trans (hconeLower.trans hconeUpper)⟩

end EditApproximation

end OAI
