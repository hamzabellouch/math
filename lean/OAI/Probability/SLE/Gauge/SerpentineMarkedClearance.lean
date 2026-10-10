import OAI.Probability.SLE.Gauge.SerpentineExteriorBounds
import OAI.Probability.SLE.Gauge.SerpentineMarkedRegion
import OAI.Probability.SLE.Geometry.MarkedRouteClearance

namespace OAI

/-! Actual fitted ribbon points satisfy the geometric separation
conditions for the two marked-point exit routes. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

theorem physicalFitChart_markedRoutes_clearance {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (w : ℂ) (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) (hwr : 0 ≤ w.re)
    {m : ℕ} (hm : 0 < m) {z : ℂ} (hz : z ∈ closedRibbon)
    (hheight : (physicalFitChart s w m z).im ≤ 2) (t : ℝ) :
    s / 20 ≤ dist (markedLeftRoute w (s / 20) t) (physicalFitChart s w m z) ∧
    s / 20 ≤ dist (markedRightRoute w (s / 20) t) (physicalFitChart s w m z) := by
  apply markedRoutes_past_clearance (by linarith)
    ((Complex.re_le_norm w).trans hw1) ((Complex.im_le_norm w).trans hw1)
    (by positivity) (by linarith)
    (physicalFitChart_re_bounds hs hs1 w hw hw1 hm hz) hheight
  rcases physicalFitChart_low_or_right hs w hw hm hz.2 with hlo | hright
  · left
    linarith
  · right
    rw [abs_of_nonneg hwr] at hright
    linarith

end SLEExactGauge.Serpentine

end

end OAI
