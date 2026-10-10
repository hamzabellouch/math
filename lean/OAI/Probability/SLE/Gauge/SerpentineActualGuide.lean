import OAI.Probability.SLE.Gauge.SerpentinePhysicalGeometry
import OAI.Probability.SLE.Gauge.SerpentineMarkedRouteClearance
import OAI.Probability.SLE.Geometry.ActualWaypointStraightening

namespace OAI

/-! The concrete terminal access guide lies in the actual surviving
component of a successful stopped serpentine trace. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

lemma physicalFit_prefix_low_right {s : ℝ} (hs : 0 < s) (w : ℂ) (hw : s ≤ w.im)
    (hwr : 0 ≤ w.re) {m : ℕ} (hm : 0 < m)
    (γ xp : ℝ≥0 → ℂ) (T : ℝ≥0)
    (hcoords : MapsTo xp (Icc 0 T) closedRibbon)
    (hγ : EqOn γ (physicalFitChart s w m ∘ xp) (Icc 0 T)) :
    ∀ q ∈ γ '' Icc 0 T, q.im ≤ w.im - 2 * (s / 20) ∨ w.re + 2 * (s / 20) ≤ q.re := by
  rintro q ⟨t, ht, rfl⟩
  rw [hγ ht]
  rcases physicalFitChart_low_or_right hs w hw hm (hcoords ht).2 with hlo | hright
  · left
    change (physicalFitChart s w m (xp t)).im ≤ _
    linarith
  · right
    rw [abs_of_nonneg hwr] at hright
    change _ ≤ (physicalFitChart s w m (xp t)).re
    linarith

theorem completeMarkedAccess_survives {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (w : ℂ) (hw : s ≤ w.im) (hw1 : ‖w‖ ≤ 1) (hwr : 0 ≤ w.re)
    {m : ℕ} (hm : 0 < m) {x : ℝ} (hx : |x| ≤ 1 / 4)
    (γ xp : ℝ≥0 → ℂ) (T : ℝ≥0)
    (hcoords : MapsTo xp (Icc 0 T) closedRibbon)
    (hγ : EqOn γ (physicalFitChart s w m ∘ xp) (Icc 0 T))
    (hfront : ∀ t ∈ Icc 0 T, (xp t).re ≤ fitCompletion s w m) :
    ∀ u : ℝ≥0, 0 < u → completeMarkedAccess s w m x u ∈ survivingDomain γ T := by
  obtain ⟨hP, hi, hH, hescape⟩ := physicalFitChart_geometry hs w hw hm
  have hpast : γ '' Icc 0 T ⊆ physicalFitChart s w m ''
      {z ∈ closedRibbon | z.re ≤ fitCompletion s w m} := by
    rintro q ⟨t, ht, rfl⟩
    exact ⟨xp t, ⟨hcoords ht, hfront t ht⟩, (hγ ht).symm⟩
  have hfuture := futureRibbon_survives _ hP.continuousOn hi
    (Nat.cast_nonneg (fitCompletion s w m)) hH γ T hpast
    (futureRibbon_unbounded_of_centerline_escape _ (fitCompletion s w m) hescape)
  have hwi := (Complex.im_le_norm w).trans hw1
  have hR : w.re < fitTerminalX s w := by
    unfold fitTerminalX
    rw [abs_of_nonneg hwr]
    linarith
  have hhook := markedHook_survives γ T w (lt_of_lt_of_le hs hw) hR
    (show w.im < 2 by linarith) (show 0 < s / 20 by positivity) (by
      rintro q ⟨t, ht, rfl⟩
      rw [hγ ht]
      refine ⟨physicalFitChart_finite_height_lt_two hs hs1 w hw hw1 hm (hcoords ht) (hfront t ht), ?_⟩
      rcases physicalFitChart_low_or_right hs w hw hm (hcoords ht).2 with hlo | hright
      · left
        change (physicalFitChart s w m (xp t)).im < w.im
        linarith
      · right
        rw [abs_of_nonneg hwr] at hright
        change w.re < (physicalFitChart s w m (xp t)).re
        linarith)
  intro u hu
  by_cases huT : (u : ℝ) ≤ fitHighTime s w m
  · rw [completeMarkedAccess, appendMarkedHook, curveJoin_of_le huT]
    apply hfuture
    exact mem_image_of_mem _ (guideCoordinate_mem_future hx (by exact_mod_cast hu))
  · rw [completeMarkedAccess, appendMarkedHook, curveJoin_of_gt (lt_of_not_ge huT)]
    exact hhook ⟨⟨(u : ℝ) - fitHighTime s w m, by linarith⟩, rfl⟩

end SLEExactGauge.Serpentine

end

end OAI
