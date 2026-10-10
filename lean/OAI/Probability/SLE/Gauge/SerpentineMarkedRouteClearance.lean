import OAI.Probability.SLE.Gauge.SerpentineMarkedLocal
import OAI.Probability.SLE.Geometry.MarkedRouteEarlyClearance

namespace OAI

/-! The two exit routes avoid every point of the complete marked access
guide by one uniform margin, including its distant initial prefix. -/

noncomputable section
open Set Metric

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

lemma terminalAccess_bounds {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (w : ℂ) (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) (hwr : 0 ≤ w.re)
    {m : ℕ} (hm : 0 < m) {x u : ℝ} (hx : |x| ≤ 1)
    (hu : u ∈ Icc (0 : ℝ) (fitHighTime s w m)) :
    -2 ≤ (terminalAccess s w m x u).re ∧ (terminalAccess s w m x u).re ≤ 2 ∧
    (terminalAccess s w m x u).im ≤ 2 ∧ w.re + s / 5 ≤ (terminalAccess s w m x u).re := by
  have hz : guideCoordinate (fitCompletion s w m) x u ∈ closedRibbon := by
    refine ⟨?_, (guideCoordinate_im_bound hu.1).trans hx⟩
    rw [guideCoordinate_re]
    exact add_nonneg (Nat.cast_nonneg _) hu.1
  have hre := physicalFitChart_re_bounds hs hs1 w hw hw1 hm hz
  exact ⟨hre.1, hre.2, physicalFitChart_terminal_guide_height hs w hw hm x hu,
    terminalAccess_right hs w hw hwr hm hx hu.1⟩

/-- A margin independent of the number of serpentine columns. -/
theorem completeMarkedAccess_route_clearance {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (w : ℂ) (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) (hwr : 0 ≤ w.re)
    {m : ℕ} (hm : 0 < m) {x t u : ℝ} (hx : |x| ≤ 1) (ht : 1 / 64 ≤ t) (hu : 0 ≤ u) :
    (s / 20) / 1000 ≤ dist (markedLeftRoute w (s / 20) t) (completeMarkedAccess s w m x u) ∧
    (s / 20) / 1000 ≤ dist (markedRightRoute w (s / 20) t) (completeMarkedAccess s w m x u) := by
  have hwr1 := (Complex.re_le_norm w).trans hw1
  have hwi1 := (Complex.im_le_norm w).trans hw1
  have ha : 0 < s / 20 := by positivity
  have ha1 : s / 20 ≤ 1 := by linarith
  by_cases huT : u ≤ fitHighTime s w m
  · rw [completeMarkedAccess, appendMarkedHook, curveJoin_of_le huT]
    have hb := terminalAccess_bounds hs hs1 w hw hw1 hwr hm hx ⟨hu, huT⟩
    have hq : w.re + 2 * (s / 20) ≤ (terminalAccess s w m x u).re := by linarith [hb.2.2.2]
    have hh := markedRoutes_past_clearance (w := w) (q := terminalAccess s w m x u)
      (t := t) (by linarith) hwr1 hwi1 ha.le ha1 ⟨hb.1, hb.2.1⟩ hb.2.2.1 (Or.inr hq)
    constructor <;> linarith [hh.1, hh.2]
  · rw [completeMarkedAccess, appendMarkedHook, curveJoin_of_gt (lt_of_not_ge huT)]
    have hR : w.re < fitTerminalX s w := by
      unfold fitTerminalX
      rw [abs_of_nonneg hwr]
      linarith
    have hR2 : fitTerminalX s w ≤ 2 := by
      unfold fitTerminalX
      rw [abs_of_nonneg hwr]
      linarith
    have hh := markedRoutes_hook_clearance_early hwr hwr1 hwi1 hR hR2 ha ha1 ht
      (show 0 ≤ u - fitHighTime s w m by linarith)
    constructor <;> linarith [hh.1, hh.2]

end SLEExactGauge.Serpentine

end

end OAI
