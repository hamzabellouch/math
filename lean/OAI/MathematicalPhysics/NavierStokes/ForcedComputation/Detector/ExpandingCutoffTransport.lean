import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingMovingCutoff
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateMotion

namespace OAI

/-! The concentration test is constant wherever a moving gate can fail
to be a rigid translation. This gives exact transport cancellation. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows VelocityDetector Set Filter
open scoped ContDiff Topology

theorem concentrationCutoff_joint_smooth (R : ℝ) {c : ℝ → Plane}
    (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => concentrationCutoff R (c p.1) p.2) := by
  change ContDiff ℝ ∞ (fun p : ℝ × Plane => massCutoff (R⁻¹ • (p.2 - c p.1)))
  exact massCutoff_smooth.comp
    ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × Plane => R⁻¹)).smul
      (contDiff_snd.sub (hc.comp contDiff_fst)))

theorem concentrationCutoff_fderiv_zero {R : ℝ} (hR : 0 < R) {c x : Plane}
    (hx : ∃ j, R < |x j - c j|) :
    fderiv ℝ (concentrationCutoff R c) x = 0 := by
  obtain ⟨j, hj⟩ := hx
  have hn : ∀ᶠ y : Plane in 𝓝 x, R < |y j - c j| :=
    (isOpen_lt continuous_const (((continuous_apply j).sub continuous_const).abs)).mem_nhds hj
  have he : concentrationCutoff R c =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hn] with y hy
    by_contra hz
    exact (not_le_of_gt hy) (concentrationCutoff_support hR c hz j)
  rw [he.fderiv_eq, fderiv_const_apply]

theorem concentrationCutoff_transport_cancel {R : ℝ} (hR : 0 < R)
    {c : ℝ → Plane} (v : Plane → Plane) (t : ℝ)
    (hv : ∀ x, (∀ j, |x j - c t j| < 2 * R) → v x = deriv c t) (x : Plane) :
    -fderiv ℝ (concentrationCutoff R (c t)) x (deriv c t) +
      fderiv ℝ (concentrationCutoff R (c t)) x (v x) = 0 := by
  by_cases hx : ∀ j, |x j - c t j| < 2 * R
  · rw [hv x hx, neg_add_cancel]
  · push Not at hx
    obtain ⟨j, hj⟩ := hx
    have hz := concentrationCutoff_fderiv_zero hR
      (c := c t) (x := x) ⟨j, by linarith⟩
    rw [hz]
    simp only [zero_apply, neg_zero, add_zero]

def concentrationDerivative (R : ℝ) (c : ℝ → Plane) (t : ℝ) (x : Plane) : ℝ :=
  -fderiv ℝ (concentrationCutoff R (c t)) x (deriv c t)

theorem concentrationDerivative_smooth (R : ℝ) {c : ℝ → Plane}
    (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (Function.uncurry (concentrationDerivative R c)) := by
  have hφ : ContDiff ℝ ∞ (Function.uncurry (fun t x => concentrationCutoff R (c t) x)) :=
    concentrationCutoff_joint_smooth R hc
  have hv : ContDiff ℝ ∞ (deriv c) := (contDiff_infty_iff_deriv.mp hc).2
  exact ((scalar_spatial_fderiv_smooth hφ).clm_apply (hv.comp contDiff_fst)).neg

theorem concentrationDerivative_support {R : ℝ} (hR : 0 < R) (c : ℝ → Plane)
    (t : ℝ) : Function.support (concentrationDerivative R c t) ⊆
      {x | ∀ j, |x j - c t j| ≤ R} := by
  intro x hx j
  by_contra hn
  have hz := concentrationCutoff_fderiv_zero hR
    (c := c t) (x := x) ⟨j, lt_of_not_ge hn⟩
  apply hx
  simp only [concentrationDerivative, hz, zero_apply, neg_zero]

end ForcedComputation.ExpandingDetector

end

end OAI
