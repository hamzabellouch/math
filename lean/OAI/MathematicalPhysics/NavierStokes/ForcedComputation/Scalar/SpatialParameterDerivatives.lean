import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlanePeriodicBounds
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace OAI

/-! Joint smoothness and periodicity of spatial derivatives with a time parameter. -/

noncomputable section
namespace ForcedComputation
open ShearFlows
open scoped ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restrict the total derivative to spatial directions. -/
def spatialParameterDerivative (n : ℕ) (f : ℝ × Plane → F) (p : ℝ × Plane) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => Plane) F :=
  (iteratedFDeriv ℝ n f p).compContinuousLinearMap
    (fun _ => ContinuousLinearMap.inr ℝ ℝ Plane)

theorem spatialParameterDerivative_eq {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (t : ℝ) (x : Plane) :
    spatialParameterDerivative n f (t,x) =
      iteratedFDeriv ℝ n (fun y : Plane => f (t,y)) x := by
  let g : ℝ × Plane → F := fun p => f ((t, (0 : Plane))+p)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  have h := (ContinuousLinearMap.inr ℝ ℝ Plane).iteratedFDeriv_comp_right
    hg x (i := n) (by simp)
  simpa [g, spatialParameterDerivative, Function.comp_def,
    iteratedFDeriv_comp_add_left] using h.symm

theorem spatialParameterDerivative_smooth {f : ℝ × Plane → F}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) : ContDiff ℝ ∞ (spatialParameterDerivative n f) := by
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (F := F) (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ Plane)).contDiff.comp
      (hf.iteratedFDeriv_right (i := n) (by simp))

theorem planePeriodic_iteratedFDeriv {f : Plane → F} (hp : PlanePeriodic f) (n : ℕ) :
    PlanePeriodic (iteratedFDeriv ℝ n f) := by
  intro x k
  have he : (fun y : Plane => f (y+fun j => (k j : ℝ))) = f := funext (fun y => hp y k)
  have h := congrArg (fun g : Plane → F => iteratedFDeriv ℝ n g x) he
  rw [iteratedFDeriv_comp_add_right] at h
  exact h

end ForcedComputation

end

end OAI
