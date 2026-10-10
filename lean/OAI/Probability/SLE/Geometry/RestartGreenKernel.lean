import OAI.Probability.SLE.Geometry.RestartConformalRadius
import OAI.Probability.SLE.Loewner.ActualRadiusStops

namespace OAI

/-! The finite centered density after a genuine restart. Only forward
composition is needed: a live source radius level gives the physical level,
and a source path that never reaches the level contributes zero density. -/

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma IsCapacityTwoWitness.restart_initial_radius
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T + t) - U T) β G' F')
    (z : ℂ) (hz : z ∈ upperHalfPlane) :
    fullRadius G T (F T (z + (U T : ℂ))) =
      ‖deriv (F T) (z + (U T : ℂ))‖ * (2 * z.im) := by
  have hUp : Continuous (fun t => U (T + t) - U T) :=
    (hU.comp (continuous_const.add continuous_id)).sub continuous_const
  simpa only [add_zero, hb.fullRadius_initial hUp z (hb.live_initial hz)] using
    hw.restart_radius_composition hU T hb 0 z (hb.live_initial hz)

lemma IsCapacityTwoWitness.restart_inverse_derivative_norm_pos
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T + t) - U T) β G' F')
    (z : ℂ) (hz : z ∈ upperHalfPlane) :
    0 < ‖deriv (F T) (z + (U T : ℂ))‖ := by
  have hzH : z + (U T : ℂ) ∈ upperHalfPlane := by
    simpa only [upperHalfPlane, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, add_zero] using hz
  have hp := hw.fullRadius_positive hU T _ (hw.2.2.2.2.2.2.1 T hzH)
  rw [hw.restart_initial_radius hU T hb z hz] at hp
  exact (mul_pos_iff.mp hp).resolve_right (by simp [not_lt.mpr (norm_nonneg _)]) |>.1

lemma IsCapacityTwoWitness.restart_green_composition
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T + t) - U T) β G' F')
    (κ : ℝ) (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain β t) :
    greenDensity κ U γ G (T + t) (F T (z + (U T : ℂ))) =
      ‖deriv (F T) (z + (U T : ℂ))‖ ^ (-codimension κ) *
        greenDensity κ (fun t => U (T + t) - U T) β G' t z := by
  have hUp : Continuous (fun t => U (T + t) - U T) :=
    (hU.comp (continuous_const.add continuous_id)).sub continuous_const
  rw [greenDensity, ite_eq_left (hw.restart_forward_composition T hb t z hz).1,
    hw.restart_radius_composition hU T hb t z hz,
    hw.restart_centered_value T hb t z hz,
    Real.mul_rpow (norm_nonneg _) (hb.fullRadius_positive hUp t z hz).le,
    greenDensity, ite_eq_left hz, mul_assoc]

lemma IsCapacityTwoWitness.restart_green_initial
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T + t) - U T) β G' F')
    (κ : ℝ) (z : ℂ) (hz : z ∈ upperHalfPlane) :
    greenDensity κ U γ G T (F T (z + (U T : ℂ))) =
      ‖deriv (F T) (z + (U T : ℂ))‖ ^ (-codimension κ) * initialGreen κ z := by
  have hUp : Continuous (fun t => U (T + t) - U T) :=
    (hU.comp (continuous_const.add continuous_id)).sub continuous_const
  simpa only [add_zero, hb.green_initial hUp (by simp) κ hz] using
    hw.restart_green_composition hU T hb κ 0 z (hb.live_initial hz)

lemma IsCapacityTwoWitness.restart_level_of_live_source
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T + t) - U T) β G' F')
    (z : ℂ) (u v : ℝ)
    (hbase : fullRadius G T (F T (z + (U T : ℂ))) =
      (2 * (F T (z + (U T : ℂ))).im) * Real.exp (-u))
    (t : ℝ≥0) (hz : z ∈ survivingDomain β t)
    (hlevel : fullRadius G' t z = (2 * z.im) * Real.exp (-v)) :
    fullRadius G (T + t) (F T (z + (U T : ℂ))) =
      (2 * (F T (z + (U T : ℂ))).im) * Real.exp (-(u + v)) ∧
    radiusLevelTime γ G (F T (z + (U T : ℂ))) (u + v) = (T + t : ℝ≥0) := by
  have he : fullRadius G (T + t) (F T (z + (U T : ℂ))) =
      (2 * (F T (z + (U T : ℂ))).im) * Real.exp (-(u + v)) := by
    rw [hw.restart_radius_composition hU T hb t z hz, hlevel,
      ← mul_assoc, ← hw.restart_initial_radius hU T hb z hz.1.1, hbase,
      neg_add, Real.exp_add]
    ring
  exact ⟨he, radiusLevelTime_eq_of_live_level hU hw _ _ _
    (hw.restart_forward_composition T hb t z hz).1 he⟩

/-- Pointwise domination suffices for conditional lower bounds. On every
source path which reaches its radius level, this is an equality. -/
theorem IsCapacityTwoWitness.restart_stopped_green_lower
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T + t) - U T) β G' F')
    (κ : ℝ) (z : ℂ) (hz : z ∈ upperHalfPlane) (u v : ℝ)
    (hbase : fullRadius G T (F T (z + (U T : ℂ))) =
      (2 * (F T (z + (U T : ℂ))).im) * Real.exp (-u)) :
    greenDensity κ U γ G T (F T (z + (U T : ℂ))) *
        (stoppedGreen κ (fun t => U (T + t) - U T) β G' z v / initialGreen κ z) ≤
      stoppedGreen κ U γ G (F T (z + (U T : ℂ))) (u + v) := by
  have hUp : Continuous (fun t => U (T + t) - U T) :=
    (hU.comp (continuous_const.add continuous_id)).sub continuous_const
  by_cases hfinite : radiusLevelTime β G' z v < ∞
  · obtain ⟨t, ht, hR⟩ := exists_live_level_of_radiusLevelTime_lt_top β G' z v hfinite
    have hphysical := hw.restart_level_of_live_source hU T hb z u v hbase t ht hR
    rw [stoppedGreen_eq_of_live_level hUp hb κ z v t ht hR,
      stoppedGreen_eq_of_live_level hU hw κ _ _ (T + t)
        (hw.restart_forward_composition T hb t z ht).1 hphysical.1,
      hw.restart_green_composition hU T hb κ t z ht,
      hw.restart_green_initial hU T hb κ z hz]
    exact le_of_eq (by field_simp [(initialGreen_pos κ z hz).ne'])
  · simp only [stoppedGreen, ite_eq_right hfinite, zero_div, mul_zero]
    exact stoppedGreen_nonneg hw κ _ _

end SLEExactGauge

end

end OAI
