import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingCenterSize

namespace OAI

/-! Uniform bounds for every time derivative of the gate velocity retain
one reciprocal duration factor, including the zeroth velocity derivative. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows
open scoped ContDiff

theorem deriv_component {c : ℝ → Plane} (hc : ContDiff ℝ ∞ c) (j : Fin 2) (t : ℝ) :
    deriv (fun s => c s j) t = deriv c t j := by
  have hd := (ContinuousLinearMap.proj j : Plane →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
    ((hc.differentiable (by simp) t).hasDerivAt)
  exact hd.deriv

theorem iteratedDeriv_velocity_component {c : ℝ → Plane} (hc : ContDiff ℝ ∞ c)
    (j : Fin 2) (i : ℕ) (t : ℝ) :
    iteratedDeriv i (fun s => deriv c s j) t =
      iteratedDeriv (i+1) (fun s => c s j) t := by
  have he : (fun s => deriv c s j) = deriv (fun s => c s j) :=
    funext (fun s => (deriv_component hc j s).symm)
  rw [he, iteratedDeriv_succ']

theorem scheduledVelocity_joint_jet {C B S S' T : ℝ} {m i : ℕ}
    (hC0 : 0 ≤ C)
    (hC : ∀ q ≤ m+1, ∀ t, |iteratedDeriv q (smoothRamp 0 1) t| ≤ C)
    (hS : 0 ≤ S) (hSS : S ≤ S') (hB : 0 ≤ B) (hT : 1 ≤ T)
    (hi : i ≤ m) (a : ℝ) (k target : ℕ)
    (hk : (k : ℝ) ≤ B) (ht : (target : ℝ) ≤ B)
    (terminal : Bool) (j : Fin 2) (y : ℝ × Plane) :
    ‖iteratedFDeriv ℝ i
      (fun p : ℝ × Plane => deriv (scheduledCenter a T S S' k target terminal) p.1 j) y‖ ≤
      (4*S'*(B+2)) * ((6 : ℝ)^(m+1)/T*C) := by
  have hc := scheduledCenter_smooth a T S S' k target terminal
  have hv : ContDiff ℝ ∞ (fun s => deriv (scheduledCenter a T S S' k target terminal) s j) :=
    (contDiff_apply ℝ ℝ j).comp ((contDiff_infty_iff_deriv.mp hc).2)
  apply (time_comp_jet_bound hv i y).trans
  rw [Real.norm_eq_abs, iteratedDeriv_velocity_component hc]
  exact scheduledCenter_coordinate_jet_bound hC0 hC hS hSS hB hT
    (by omega) (by omega) a k target hk ht terminal j y.1

end ForcedComputation.ExpandingDetector

end

end OAI
