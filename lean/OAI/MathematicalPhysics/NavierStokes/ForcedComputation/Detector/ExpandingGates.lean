import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateGeometry
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarHamiltonian

namespace OAI

/-! The local Hamiltonian translation gate used at each finite address.
Its plateau is exact and its support is inherited from the cutoff. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Set Filter
open scoped ContDiff Topology

theorem field_translate (H : Plane → ℝ) (c x : Plane) :
    PlanarHamiltonian.field (fun y => H (y - c)) x =
      PlanarHamiltonian.field H (x - c) := by
  unfold PlanarHamiltonian.field PlanarHamiltonian.spatialD
  simp only [fderiv_comp_sub]

def translationGate (χ : Plane → ℝ) (c v : Plane) : Plane → Plane :=
  PlanarHamiltonian.field
    (fun x => χ (x - c) * PlanarHamiltonian.translationPotential v (x - c))

theorem translationGate_smooth {χ : Plane → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (c v : Plane) : ContDiff ℝ ∞ (translationGate χ c v) :=
  PlanarHamiltonian.field_smooth
    ((hχ.comp (contDiff_id.sub contDiff_const)).mul
      ((PlanarHamiltonian.translationPotential_smooth v).comp
        (contDiff_id.sub contDiff_const)))

theorem translationGate_solenoidal {χ : Plane → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (c v x : Plane) : PlanarHamiltonian.divergence (translationGate χ c v) x = 0 :=
  PlanarHamiltonian.field_divergence
    ((hχ.comp (contDiff_id.sub contDiff_const)).mul
      ((PlanarHamiltonian.translationPotential_smooth v).comp
        (contDiff_id.sub contDiff_const))) x

theorem translationGate_plateau {χ : Plane → ℝ} (c v x : Plane)
    (hχ : χ =ᶠ[𝓝 (x - c)] fun _ => 1) : translationGate χ c v x = v := by
  unfold translationGate
  have hc : (fun y => χ (y - c)) =ᶠ[𝓝 x] fun _ => 1 :=
    hχ.comp_tendsto (continuous_id.sub continuous_const).continuousAt
  rw [PlanarHamiltonian.field_cutoff_plateau _ _ hc, field_translate,
    PlanarHamiltonian.field_translation]

theorem translationGate_support (χ : Plane → ℝ) (c v : Plane) :
    tsupport (translationGate χ c v) ⊆ tsupport (fun x => χ (x - c)) :=
  (PlanarHamiltonian.field_tsupport _).trans (tsupport_mul_subset_left)

theorem translationGate_compactSupport {χ : Plane → ℝ} (hχ : HasCompactSupport χ)
    (c v : Plane) : HasCompactSupport (translationGate χ c v) := by
  have hc : HasCompactSupport (fun x => χ (x - c)) := by
    simpa only [Function.comp_def, Homeomorph.coe_addRight, sub_eq_add_neg] using
      hχ.comp_homeomorph (Homeomorph.addRight (-c))
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  exact translationGate_support χ c v

end ForcedComputation.ExpandingDetector

end

end OAI
