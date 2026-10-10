import OAI.Probability.SLE.Geometry.MarkedTubeLocalSides
import OAI.Probability.SLE.Geometry.PhysicalRouteProbability

namespace OAI

/-! Compress the four-leg marked routes into the finite Brownian exit
window used by the published conformal exit law. -/

noncomputable section
open Set Metric MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates Target

def markedWindowRoute (right : Bool) (w : ℂ) (a t : ℝ) : ℂ :=
  if right then markedRightRoute w a (4 / 3 * t) else markedLeftRoute w a (4 / 3 * t)

lemma markedWindowRoute_zero (right : Bool) (w : ℂ) (a : ℝ) :
    markedWindowRoute right w a 0 = w := by
  cases right <;> simp only [markedWindowRoute, Bool.false_eq_true, ↓reduceIte, mul_zero,
    markedLeftRoute_zero, markedRightRoute_zero]

lemma markedWindowRoute_small (right : Bool) (w : ℂ) (a : ℝ) :
    markedWindowRoute right w a (1 / 64) =
      if right then markedRightRoute w a (1 / 48) else markedLeftRoute w a (1 / 48) := by
  norm_num only [markedWindowRoute]

lemma markedWindowRoute_final (right : Bool) (w : ℂ) (a : ℝ) :
    (markedWindowRoute right w a 3).im = -1 := by
  cases right <;> norm_num [markedWindowRoute, markedLeftRoute_four, markedRightRoute_final]

lemma markedWindowRoute_lipschitz (right : Bool) {w : ℂ} (hw : ‖w‖ ≤ 1)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) : LipschitzWith 32 (markedWindowRoute right w a) := by
  have hroute : LipschitzWith 24
      (fun t => if right then markedRightRoute w a t else markedLeftRoute w a t) := by
    cases right
    · exact markedLeftRoute_lipschitz hw ha ha1
    · exact markedRightRoute_lipschitz hw ha ha1
  apply LipschitzWith.of_dist_le_mul
  intro t u
  have hh := hroute.dist_le_mul (4 / 3 * t) (4 / 3 * u)
  have hd : dist (4 / 3 * t) (4 / 3 * u) = (4 / 3 : ℝ) * dist t u := by
    rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
    norm_num
  rw [hd] at hh
  change dist (markedWindowRoute right w a t) (markedWindowRoute right w a u) ≤ _
  convert hh using 1 <;> norm_num [markedWindowRoute]; ring

theorem uniform_marked_window_tube_probability
    (hpublished : PublishedPlanarWienerUnitSupport) (W : WienerLaw) (hW : IsWiener W)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ (right : Bool) (w : ℂ), ‖w‖ ≤ 1 →
      q ≤ (W.prod W) {b | ∀ t ∈ Icc (0 : ℝ) 3,
        dist (physicalUnitBrownianPath w b t) (markedWindowRoute right w a t) < a / 10000} := by
  obtain ⟨q, hq, hprob⟩ := uniform_physical_route_tube_probability hpublished W hW 32
    (by positivity : 0 < a / 10000)
  refine ⟨q, hq, fun right w hw => ?_⟩
  simpa only [markedWindowRoute_zero] using
    hprob (markedWindowRoute right w a) (markedWindowRoute_lipschitz right hw ha.le ha1)

end SLEExactGauge.Serpentine

end

end OAI
