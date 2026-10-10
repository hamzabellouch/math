import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingRecorderMass

namespace OAI

/-! Successive concentration estimates compose along every finite
recorder execution. Only the proved per-stage diffusion losses accumulate. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector Set MeasureTheory
open scoped BigOperators

theorem recorder_steps_mass_retention
    (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) {m : ℕ} (hm : 0 < m)
    {σ D K ν C q : ℝ} (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (hν : 0 ≤ ν) (hC : 0 ≤ C) (p : Plane)
    {w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν (expandingDrift M hM blank m σ D K) (unitImpulse p) w)
    (hwi : ∀ t, 0 ≤ t → Integrable (w t))
    (hwn : ∀ t, 0 ≤ t → ∀ x, 0 ≤ w t x)
    (hwm : ∀ t, 0 ≤ t → (∫ x, w t x) ≤ 1)
    (hΔ : ∀ x, |scalarLaplacian massCutoff x| ≤ C)
    {U₀ : Configuration (State M) (Alphabet M)} (h₀ : CenteredBlank blank m U₀)
    (hq : q ≤ ∫ x, concentrationCutoff (radius σ D K 0)
      (configurationCenter M hM blank m σ D K 0 U₀) x * w 2 x)
    {n : ℕ} {U : Configuration (State M) (Alphabet M)}
    (hrun : Steps (finiteMachine M hM) n U₀ U) :
    q - (∑ i ∈ Finset.range n, ν * ((radius σ D K i)⁻¹ ^ 2 * C) * duration σ D K i) ≤
      ∫ x, concentrationCutoff (radius σ D K n)
        (configurationCenter M hM blank m σ D K n U) x * w (stageStart σ D K n) x := by
  induction hrun with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, sub_zero, stageStart_zero] using hq
  | @next n U₀ U V hrun hstep ih =>
    have ih := ih h₀ hq
    have hU : CenteredBlank blank (m + n) U := h₀.steps hm hrun
    have hs := recorder_step_mass_retention M hM blank hm hσ hD hK hν hC p
      hw hwi hwn hwm hΔ hU hstep
    rw [Finset.sum_range_succ]
    linarith

end ForcedComputation.ExpandingDetector

end

end OAI
