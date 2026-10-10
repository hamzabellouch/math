import OAI.Probability.SLE.Geometry.MarkedRouteClearance
import OAI.Probability.SLE.Geometry.MarkedCornerBounds

namespace OAI

/-! The initial portions of the two physical routes lie on opposite
sides of the explicit local corner chart. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

lemma markedLeftRoute_corner_side {w : ℂ} {a t : ℝ}
    (ha : 0 < a) (ht : t ∈ Ioc (0 : ℝ) 1) :
    0 < ((markedCornerChart w).symm (markedLeftRoute w a t)).im := by
  rw [markedCornerChart_symm_im, markedLeftRoute_re, markedLeftRoute_im,
    unitClip_of_mem ⟨ht.1.le, ht.2⟩,
    unitClip_of_nonpos (by linarith [ht.2] : t - 1 ≤ 0),
    unitClip_of_nonpos (by linarith [ht.2] : t - 2 ≤ 0)]
  have hp : 0 < a * t := mul_pos ha ht.1
  apply lt_of_lt_of_le hp
  apply le_trans _ (le_max_right _ _)
  linarith

lemma markedRightRoute_corner_side {w : ℂ} {a t : ℝ}
    (ha : 0 < a) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ((markedCornerChart w).symm (markedRightRoute w a t)).im < 0 := by
  rw [markedCornerChart_symm_im, markedRightRoute_re, markedRightRoute_im,
    unitClip_of_mem ⟨ht.1.le, ht.2⟩,
    unitClip_of_nonpos (by linarith [ht.2] : t - 1 ≤ 0),
    unitClip_of_nonpos (by linarith [ht.2] : t - 2 ≤ 0),
    unitClip_of_nonpos (by linarith [ht.2] : t - 3 ≤ 0), max_lt_iff]
  have hp : 0 < a * t := mul_pos ha ht.1
  constructor <;> nlinarith

end SLEExactGauge.Serpentine

end

end OAI
