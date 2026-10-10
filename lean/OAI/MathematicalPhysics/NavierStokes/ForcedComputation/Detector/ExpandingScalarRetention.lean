import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingScalar
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingInitialCapture
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingFiniteRetention

namespace OAI

/-! Conditional scalar construction with a quantitative bound along
every actual recorder prefix. The sole analytic assumption is the stated
published scalar existence input. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector Set MeasureTheory
open scoped BigOperators

theorem expanding_scalar_retention (hE : PlaneScalarExistence)
    (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) {m : ℕ} (hm : 0 < m)
    (U₀ : Configuration (State M) (Alphabet M)) (h₀ : CenteredBlank blank m U₀)
    {σ D K ν C : ℝ} (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (hν : 0 < ν) (hC : 0 ≤ C) (hΔ : ∀ x, |scalarLaplacian massCutoff x| ≤ C) :
    ∃ w : ℝ → Plane → ℝ,
      GlobalPlaneScalarSolution ν (expandingDrift M hM blank m σ D K)
        (unitImpulse (configurationCenter M hM blank m σ D K 0 U₀)) w ∧
      (∀ t, 0 ≤ t → ∀ x, 0 ≤ w t x) ∧
      (∀ t, 0 ≤ t → Integrable (w t)) ∧
      (∀ t, 0 ≤ t → (∫ x, w t x) = smoothRamp 0 1 t) ∧
      ∀ n U, Steps (finiteMachine M hM) n U₀ U →
        1 - ν * ((radius σ D K 0)⁻¹ ^ 2 * C) * 2 -
          (∑ i ∈ Finset.range n, ν * ((radius σ D K i)⁻¹ ^ 2 * C) * duration σ D K i) ≤
        ∫ x, concentrationCutoff (radius σ D K n)
          (configurationCenter M hM blank m σ D K n U) x * w (stageStart σ D K n) x := by
  let p := configurationCenter M hM blank m σ D K 0 U₀
  obtain ⟨w, hw, hwn, hwi, hmass⟩ := unitImpulse_scalar_exists hE ν hν
    (expandingDrift M hM blank m σ D K) p
    (expandingDrift_smooth M hM blank m hσ hD hK)
    (expandingDrift_compact_coefficients M hM blank m hσ hD hK p)
    (expandingDrift_divergence M hM blank m hσ hD hK)
  have hwm (t : ℝ) (ht : 0 ≤ t) : (∫ x, w t x) ≤ 1 :=
    unitImpulse_mass_le_one hmass ht
  have hc := initial_concentration_capture p (hw 2 (by norm_num)) hν.le
    (radius_ge_one hσ hD hK 0) hC
    (expandingDrift_smooth M hM blank m hσ hD hK)
    (expandingDrift_divergence M hM blank m hσ hD hK) hΔ
    (fun t ht => hwi t ht.1) (fun t ht => hwn t ht.1) (fun t ht => hwm t ht.1)
    (by norm_num : (0 : ℝ) ≤ 2) le_rfl
    (fun t ht => funext (fun x => expandingDrift_initial M hM blank m hσ hD hK ht.2.le x))
  have hq : 1 - ν * ((radius σ D K 0)⁻¹ ^ 2 * C) * 2 ≤
      ∫ x, concentrationCutoff (radius σ D K 0) p x * w 2 x := by
    simpa only [smoothRamp_after (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 2)] using hc
  refine ⟨w, hw, hwn, hwi, hmass, ?_⟩
  intro n U hrun
  exact recorder_steps_mass_retention M hM blank hm hσ hD hK hν.le hC p
    hw hwi hwn hwm hΔ h₀ hq hrun

end ForcedComputation.ExpandingDetector

end

end OAI
