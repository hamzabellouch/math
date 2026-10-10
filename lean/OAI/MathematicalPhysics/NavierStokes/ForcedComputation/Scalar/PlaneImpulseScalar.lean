import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneMassConservation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneUnitImpulse

namespace OAI

/-! The actual unit impulse has nonnegative integrable scalar evolution,
with total mass exactly the prescribed smooth injection ramp. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows VelocityDetector Set MeasureTheory
open scoped ContDiff

theorem unitImpulse_scalar_exists (hE : PlaneScalarExistence)
    (ν : ℝ) (hν : 0 < ν) (a : ℝ → Plane → Plane) (p : Plane)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hc : CompactPlaneCoefficients a (unitImpulse p))
    (hdiv : ∀ t x, PlanarHamiltonian.divergence (a t) x = 0) :
    ∃ w : ℝ → Plane → ℝ, GlobalPlaneScalarSolution ν a (unitImpulse p) w ∧
      (∀ t, 0 ≤ t → ∀ x, 0 ≤ w t x) ∧
      (∀ t, 0 ≤ t → Integrable (w t)) ∧
      (∀ t, 0 ≤ t → (∫ x, w t x) = smoothRamp 0 1 t) := by
  obtain ⟨w, hw⟩ := hE.global ν hν a (unitImpulse p) ha (unitImpulse_smooth p) hc
  have hn : ∀ t, 0 ≤ t → ∀ x, 0 ≤ w t x :=
    hw.nonnegative hν.le ha hc (fun t _ x => unitImpulse_nonneg p t x)
  refine ⟨w, hw, hn, ?_, ?_⟩
  · intro t ht
    exact (hw t ht).integrable ht hν.le ha (unitImpulse_smooth p) hc
      (fun s _ x => unitImpulse_nonneg p s x) t ⟨ht, le_rfl⟩
  · intro t ht
    apply (hw t ht).mass_eq_source ht hν.le ha (unitImpulse_smooth p) hc hdiv
      (fun s _ x => unitImpulse_nonneg p s x)
      (smoothRamp_smooth 0 1).continuous.continuousOn
      (smoothRamp_before (by norm_num) le_rfl)
    intro s _
    rw [unitImpulse_mass]
    exact ((smoothRamp_smooth 0 1).differentiable (by simp) s).hasDerivAt

theorem unitImpulse_mass_after {w : ℝ → Plane → ℝ}
    (hm : ∀ t, 0 ≤ t → (∫ x, w t x) = smoothRamp 0 1 t)
    {t : ℝ} (ht : 1 ≤ t) : (∫ x, w t x) = 1 := by
  rw [hm t (by linarith), smoothRamp_after (by norm_num) ht]

theorem unitImpulse_mass_le_one {w : ℝ → Plane → ℝ}
    (hm : ∀ t, 0 ≤ t → (∫ x, w t x) = smoothRamp 0 1 t)
    {t : ℝ} (ht : 0 ≤ t) : (∫ x, w t x) ≤ 1 := by
  rw [hm t ht]
  exact (smoothRamp_range 0 1 t).2

end ForcedComputation.ExpandingDetector

end

end OAI
