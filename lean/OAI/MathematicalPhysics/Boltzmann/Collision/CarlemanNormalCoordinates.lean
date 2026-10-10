import OAI.MathematicalPhysics.Boltzmann.Branching.RedundantPlaneIntegral
import OAI.MathematicalPhysics.Boltzmann.Model

namespace OAI

section

/-!
# Energy algebra on a Carleman collision plane

These are the exact geometric and Gaussian identities used in Section 3.
The coarea/disintegration formula expressing the gain as a plane integral
is a separate theorem and is not assumed or asserted here.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

/-- The unobserved outgoing velocity is fixed by momentum conservation. -/
def companionVelocity (p ξ v : Velocity) : Velocity := p + ξ - v

/-- The plane equation in the Carleman representation is exactly the energy equation. -/
theorem carleman_energy (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    ‖p‖ ^ 2 + ‖ξ‖ ^ 2 = ‖v‖ ^ 2 + ‖companionVelocity p ξ v‖ ^ 2 := by
  unfold companionVelocity
  rw [norm_sub_sq_real, norm_add_sq_real, inner_add_left]
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq] at h
  rw [← real_inner_comm ξ v]
  nlinarith only [h]

/-- The observed speed is bounded by the total incoming energy. -/
theorem carleman_observed_energy_le (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    ‖v‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖ξ‖ ^ 2 := by
  have he := carleman_energy p ξ v h
  nlinarith only [he, sq_nonneg ‖companionVelocity p ξ v‖]

/-- Squared Japanese-bracket inequality used to transfer the polynomial weight. -/
theorem carleman_bracket_sq_le (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    1 + ‖v‖ ^ 2 ≤ (1 + ‖p‖ ^ 2) * (1 + ‖ξ‖ ^ 2) := by
  have he := carleman_observed_energy_le p ξ v h
  nlinarith only [he, mul_nonneg (sq_nonneg ‖p‖) (sq_nonneg ‖ξ‖)]

theorem carleman_bracket_le (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    Real.sqrt (1 + ‖v‖ ^ 2) ≤
      Real.sqrt (1 + ‖p‖ ^ 2) * Real.sqrt (1 + ‖ξ‖ ^ 2) := by
  have he := Real.sqrt_le_sqrt (carleman_bracket_sq_le p ξ v h)
  rwa [Real.sqrt_mul (by positivity : 0 ≤ 1 + ‖p‖ ^ 2)] at he

/-- The Gaussian ratio identity in equation `ker:energy-factor`. -/
theorem carleman_gaussian_ratio (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    Real.exp (-‖ξ‖ ^ 2) / Real.exp (-‖v‖ ^ 2) =
      Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) := by
  rw [← Real.exp_sub]
  congr 1
  have he := carleman_energy p ξ v h
  linarith only [he]

end BoltzmannNonuniqueness

end

end

section

/-! # Normal and tangent coordinates for the Carleman change of variables -/
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ENNReal
namespace BoltzmannNonuniqueness.CarlemanCoordinates

abbrev V := Fin 3 → ℝ

def frameMatrix (n : V) (r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-n 0, -n 2*n 0/r^2, -n 1/r;
      -n 1, -n 2*n 1/r^2, n 0/r;
      -n 2, 1, 0]

def frame (n : V) (r : ℝ) : V →ₗ[ℝ] V := (frameMatrix n r).toLin'

theorem frame_apply (n q : V) (r : ℝ) :
    frame n r q = ![-q 0*n 0-q 1*n 2*n 0/r^2-q 2*n 1/r,
      -q 0*n 1-q 1*n 2*n 1/r^2+q 2*n 0/r,-q 0*n 2+q 1] := by
  ext i
  fin_cases i <;> simp [frame,frameMatrix,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem frameMatrix_det {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) :
    (frameMatrix n r).det = RedundantPlane.normSq n/r := by
  simp [frameMatrix,Matrix.det_fin_three,RedundantPlane.normSq]
  field_simp [hr.ne']
  linear_combination -(n 2)^2 * hrsq

theorem frame_dot {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) (q : V) :
    n ⬝ᵥ frame n r q = -q 0*RedundantPlane.normSq n := by
  rw [frame_apply]
  simp [RedundantPlane.normSq,Matrix.vecHead,Matrix.vecTail]
  field_simp [hr.ne']
  linear_combination (q 1*n 2) * hrsq

theorem frame_map_volume {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) :
    Measure.map (frame n r) volume = ENNReal.ofReal (r/RedundantPlane.normSq n) • volume := by
  have hN := RedundantPlane.normSq_pos hr hrsq
  have hd := frameMatrix_det hr hrsq
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (hd.trans_ne (ne_of_gt (div_pos hN hr)))
  simpa only [frame,hd,inv_div,abs_of_pos (div_pos hr hN)] using hm

theorem unit_frame_map_volume {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) (hn : RedundantPlane.normSq n = 1) :
    Measure.map (frame n r) volume = ENNReal.ofReal r • volume := by
  simpa only [hn,div_one] using frame_map_volume hr hrsq

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

end OAI
