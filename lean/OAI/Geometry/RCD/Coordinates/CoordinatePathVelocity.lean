import OAI.Geometry.RCD.Coordinates.FrameVelocityDefect

namespace OAI

/-! # The finite coordinate derivative along a real parameter -/

open Finset
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates

def coordinateDerivative {n : ℕ} (f : ℝ → Euclidean n) (t : ℝ) : Euclidean n :=
  WithLp.toLp 2 (fun i => deriv (fun s => f s i) t)

theorem coordinate_inner_hasDerivAt {n : ℕ} (f : ℝ → Euclidean n) {t : ℝ}
    (h : ∀ i, DifferentiableAt ℝ (fun s => f s i) t) (a : Euclidean n) :
    HasDerivAt (fun s => ⟪f s,a⟫_ℝ) ⟪coordinateDerivative f t,a⟫_ℝ t := by
  have hh := HasDerivAt.fun_sum (u := (univ : Finset (Fin n)))
    (fun i _ => (h i).hasDerivAt.const_mul (a i))
  simpa only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,coordinateDerivative] using hh

end RegularPointCoordinates

end

end OAI
