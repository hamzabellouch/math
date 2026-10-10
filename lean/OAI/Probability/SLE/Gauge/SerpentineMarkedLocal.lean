import OAI.Probability.SLE.Gauge.SerpentineMarkedGuide

namespace OAI

/-! The explicit marked access guide meets a small corner-chart disk
exactly along its real diameter. The distant terminal prefix is excluded
quantitatively, so there are no nonlocal intersections. -/

noncomputable section
open Set Metric
open scoped Topology NNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

lemma terminalAccess_distance {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    (hwr : 0 ≤ w.re) {m : ℕ} (hm : 0 < m) {x t : ℝ} (hx : |x| ≤ 1) (ht : 0 ≤ t) :
    s / 5 ≤ dist (terminalAccess s w m x t) w := by
  have hr := terminalAccess_right hs w hw hwr hm hx ht
  have hb := Complex.abs_re_le_norm (terminalAccess s w m x t - w)
  rw [Complex.sub_re, ← dist_eq_norm] at hb
  linarith [le_abs_self ((terminalAccess s w m x t).re - w.re)]

theorem completeMarkedAccess_corner_iff {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (w : ℂ) (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) (hwr : 0 ≤ w.re)
    {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : |x| ≤ 1) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) ((s / 20) / 12)) :
    (∃ t : ℝ, 0 < t ∧ completeMarkedAccess s w m x t = markedCornerChart w z) ↔ z.im = 0 := by
  have hn : ‖z‖ < (s / 20) / 12 := by simpa only [mem_ball, dist_zero_right] using hz
  have hwi : w.im ≤ 1 := (Complex.im_le_norm w).trans hw1
  have hR : w.re < fitTerminalX s w := by
    unfold fitTerminalX
    rw [abs_of_nonneg hwr]
    linarith
  have hT := fitHighTime_large hs hs1 w hw hw1 hm
  have hcorner := markedHook_small_corner_iff (w := w) (z := z) hR
    (show w.im < 2 by linarith) (show 0 < s / 20 by positivity)
    (show 0 < (s / 20) / 12 by positivity)
    (show 3 * ((s / 20) / 12) < 2 - w.im by linarith)
    (show 3 * ((s / 20) / 12) < s / 20 by linarith) hn
  constructor
  · rintro ⟨t, ht, he⟩
    by_cases htT : t ≤ fitHighTime s w m
    · rw [completeMarkedAccess, appendMarkedHook, curveJoin_of_le htT] at he
      have hd := terminalAccess_distance hs w hw hwr hm hx ht.le
      rw [he] at hd
      have hb := markedCornerChart_norm w z
      linarith
    · rw [completeMarkedAccess, appendMarkedHook, curveJoin_of_gt (lt_of_not_ge htT)] at he
      exact hcorner.mp ⟨t - fitHighTime s w m, by linarith, he⟩
  · intro him
    obtain ⟨u, hu, he⟩ := hcorner.mpr him
    refine ⟨fitHighTime s w m + u, by linarith, ?_⟩
    by_cases hu0 : u = 0
    · subst u
      rw [add_zero, completeMarkedAccess, appendMarkedHook, curveJoin_of_le le_rfl]
      change physicalFitChart s w m (guideCoordinate (fitCompletion s w m) x (fitHighTime s w m)) = _
      rw [physicalFitChart_terminal_guide_endpoint hs hs1 w hw hw1 hm x]
      simpa [markedHook_zero w hR] using he
    · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      rw [completeMarkedAccess, appendMarkedHook, curveJoin_of_gt (by linarith), add_sub_cancel_left]
      exact he

theorem completeMarkedAccess_corner_nnreal_iff {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (w : ℂ) (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) (hwr : 0 ≤ w.re)
    {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : |x| ≤ 1) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) ((s / 20) / 12)) :
    (∃ t : ℝ≥0, 0 < t ∧ completeMarkedAccess s w m x t = markedCornerChart w z) ↔ z.im = 0 := by
  rw [← completeMarkedAccess_corner_iff hs hs1 w hw hw1 hwr hm hx hz]
  constructor
  · rintro ⟨t, ht, he⟩
    exact ⟨t, by exact_mod_cast ht, he⟩
  · rintro ⟨t, ht, he⟩
    exact ⟨⟨t, ht.le⟩, by exact_mod_cast ht, he⟩

lemma completeMarkedAccess_upper {s : ℝ} (hs : 0 < s)
    (w : ℂ) (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) (hwr : 0 ≤ w.re)
    {m : ℕ} (hm : 0 < m) {x u : ℝ} (hu : 0 ≤ u) :
    completeMarkedAccess s w m x u ∈ upperHalfPlane := by
  have hwi := (Complex.im_le_norm w).trans hw1
  change 0 < (completeMarkedAccess s w m x u).im
  by_cases huT : u ≤ fitHighTime s w m
  · rw [completeMarkedAccess, appendMarkedHook, curveJoin_of_le huT]
    change 0 < (physicalFitChart s w m (guideCoordinate (fitCompletion s w m) x u)).im
    rw [physicalFitChart_terminal_guide hs w hw hm x hu]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
    have hb := (fitTerminalHeight_bounds hs w hw hm).1
    have hp := mul_nonneg (fit_width_pos hs hm).le hu
    linarith
  · rw [completeMarkedAccess, appendMarkedHook, curveJoin_of_gt (lt_of_not_ge huT)]
    have hR : w.re < fitTerminalX s w := by
      unfold fitTerminalX
      rw [abs_of_nonneg hwr]
      linarith
    have hh := markedHook_im_lower hR (show w.im < 2 by linarith)
      (show 0 < s / 20 by positivity) (show 0 ≤ u - fitHighTime s w m by linarith)
    linarith

end SLEExactGauge.Serpentine

end

end OAI
