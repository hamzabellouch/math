import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingFiniteGates
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateClock
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PullbackMass

namespace OAI

/-! Joint smoothness of the moving Hamiltonian translation gates, including
their motion through the cutoff collars. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Set Filter
open scoped ContDiff Topology

theorem timeHamiltonianField_smooth {H : ℝ → Plane → ℝ}
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) :
    ContDiff ℝ ∞ (fun y : ℝ × Plane => PlanarHamiltonian.field (H y.1) y.2) := by
  have hd := VelocityDetector.scalar_spatial_fderiv_smooth hH
  exact ((hd.clm_apply contDiff_const).smul contDiff_const).sub
    ((hd.clm_apply contDiff_const).smul contDiff_const)

theorem translationGate_zero_velocity (χ : Plane → ℝ) (c x : Plane) :
    translationGate χ c 0 x = 0 := by
  simp [translationGate, PlanarHamiltonian.translationPotential,
    PlanarHamiltonian.field, PlanarHamiltonian.spatialD]

def movingGate (R : ℝ) (c : ℝ → Plane) (t : ℝ) (x : Plane) : Plane :=
  translationGate (gateCutoff R) (c t) (deriv c t) x

theorem movingGate_smooth (R : ℝ) {c : ℝ → Plane} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (Function.uncurry (movingGate R c)) := by
  have hv : ContDiff ℝ ∞ (deriv c) := (contDiff_infty_iff_deriv.mp hc).2
  have hz : ContDiff ℝ ∞ (fun y : ℝ × Plane => y.2 - c y.1) :=
    contDiff_snd.sub (hc.comp contDiff_fst)
  change ContDiff ℝ ∞ (fun y : ℝ × Plane => PlanarHamiltonian.field
    (fun x => gateCutoff R (x - c y.1) *
      PlanarHamiltonian.translationPotential (deriv c y.1) (x - c y.1)) y.2)
  apply timeHamiltonianField_smooth (H := fun s x => gateCutoff R (x - c s) *
    PlanarHamiltonian.translationPotential (deriv c s) (x - c s))
  exact ((gateCutoff_smooth R).comp hz).mul
    ((((contDiff_apply ℝ ℝ 0).comp hv).comp contDiff_fst).mul
      ((contDiff_apply ℝ ℝ 1).comp hz) |>.sub
        ((((contDiff_apply ℝ ℝ 1).comp hv).comp contDiff_fst).mul
          ((contDiff_apply ℝ ℝ 0).comp hz)))

theorem movingGate_zero_of_constant_near (R : ℝ) {c : ℝ → Plane} {t : ℝ} {p : Plane}
    (hc : c =ᶠ[𝓝 t] fun _ => p) (x : Plane) : movingGate R c t x = 0 := by
  have hd : HasDerivAt c 0 t := (hasDerivAt_const t p).congr_of_eventuallyEq hc
  rw [movingGate, hd.deriv, translationGate_zero_velocity]

theorem movingGate_tracks {R : ℝ} (hR : 0 < R) {c : ℝ → Plane}
    (hc : ContDiff ℝ ∞ c) (z : Plane) (hz : ∀ j, |z j| < 2 * R) (t : ℝ) :
    HasDerivAt (fun s => c s + z) (movingGate R c t (c t + z)) t := by
  have hv : movingGate R c t (c t + z) = deriv c t := by
    apply translationGate_plateau
    apply gateCutoff_one_near hR
    intro j
    simpa only [Pi.add_apply, Pi.sub_apply, add_sub_cancel_left] using hz j
  rw [hv]
  exact ((hc.differentiable (by simp) t).hasDerivAt).add_const z

end ForcedComputation.ExpandingDetector

end

end OAI
