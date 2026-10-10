import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneTaylorControl
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarInput

namespace OAI

/-! Directional restrictions of the scalar retain spatial derivative bounds
on the closed time slab. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff

def scalarLine (f : Plane → ℝ) (x v : Plane) (t : ℝ) : ℝ := f (x + t • v)

theorem scalarLine_smooth {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (x v : Plane) :
    ContDiff ℝ ∞ (scalarLine f x v) :=
  hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

theorem scalarLine_iteratedDeriv {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v : Plane) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (scalarLine f x v) t =
      iteratedFDeriv ℝ n f (x + t • v) (fun _ => v) := by
  let L : ℝ →L[ℝ] Plane := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hF : ContDiff ℝ ∞ (fun y : Plane => f (x + y)) :=
    hf.comp (contDiff_const.add contDiff_id)
  change iteratedFDeriv ℝ n ((fun y : Plane => f (x + y)) ∘ L) t (fun _ => 1) = _
  rw [L.iteratedFDeriv_comp_right hF t (by simp),
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]
  simp [L]

theorem scalarLine_iteratedDeriv_bound {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v : Plane) (n : ℕ) {B : ℝ}
    (hB : ∀ y, ‖iteratedFDeriv ℝ n f y‖ ≤ B) (t : ℝ) :
    |iteratedDeriv n (scalarLine f x v) t| ≤ B * ‖v‖ ^ n := by
  rw [scalarLine_iteratedDeriv hf]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (x + t • v)‖ * ‖v‖ ^ n := by
      simpa only [Real.norm_eq_abs, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n f (x + t • v)).le_opNorm (fun _ => v)
    _ ≤ _ := mul_le_mul_of_nonneg_right (hB _) (pow_nonneg (norm_nonneg _) _)

end ForcedComputation.VelocityDetector

end

end OAI
