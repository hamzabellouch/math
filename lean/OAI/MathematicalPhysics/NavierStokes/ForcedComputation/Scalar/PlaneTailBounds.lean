import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneTailProfile

namespace OAI

/-! Explicit differential inequalities for the integrable tail profile. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set
open scoped ContDiff

theorem planeBarrierSquare_abs_coordinate (x : Plane) (j : Fin 2) :
    |x j| ≤ planeBarrierSquare x := by
  apply abs_le.mpr
  fin_cases j
  · change -(1 + (x 0) ^ 2 + (x 1) ^ 2) ≤ x 0 ∧ x 0 ≤ 1 + (x 0) ^ 2 + (x 1) ^ 2
    constructor <;> nlinarith [sq_nonneg (x 0 - 1), sq_nonneg (x 0 + 1), sq_nonneg (x 1)]
  · change -(1 + (x 0) ^ 2 + (x 1) ^ 2) ≤ x 1 ∧ x 1 ≤ 1 + (x 0) ^ 2 + (x 1) ^ 2
    constructor <;> nlinarith [sq_nonneg (x 1 - 1), sq_nonneg (x 1 + 1), sq_nonneg (x 0)]

theorem planeTailProfile_laplacian_bound (x : Plane) :
    scalarLaplacian planeTailProfile x ≤ 24 * planeTailProfile x := by
  have hp := planeBarrierSquare_pos x
  have hi : 0 ≤ (planeBarrierSquare x)⁻¹ := (inv_pos.mpr hp).le
  have hs : (x 0) ^ 2 + (x 1) ^ 2 ≤ (planeBarrierSquare x) ^ 2 := by
    unfold planeBarrierSquare
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1),
      sq_nonneg ((x 0) ^ 2 + (x 1) ^ 2)]
  have hm := mul_le_mul_of_nonneg_right hs (pow_nonneg hi 4)
  have he : planeBarrierSquare x ^ 2 * (planeBarrierSquare x)⁻¹ ^ 4 =
      planeTailProfile x := by
    unfold planeTailProfile
    field_simp [hp.ne']
  rw [he] at hm
  rw [planeTailProfile_laplacian]
  nlinarith [pow_nonneg hi 3]

theorem planeTailProfile_advection_bound {A : ℝ} (_hA : 0 ≤ A)
    (a : Plane → Plane) (ha : ∀ x, ‖a x‖ ≤ A) (x : Plane) :
    -fderiv ℝ planeTailProfile x (a x) ≤ 8 * A * planeTailProfile x := by
  have hp := planeBarrierSquare_pos x
  have hac (j : Fin 2) : |a x j| ≤ A := by
    have hnorm : |a x j| ≤ ‖a x‖ := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (a x) j)
    exact hnorm.trans (ha x)
  have hj (j : Fin 2) : x j * a x j ≤ planeBarrierSquare x * A := by
    calc
      _ ≤ |x j * a x j| := le_abs_self _
      _ = |x j| * |a x j| := abs_mul _ _
      _ ≤ planeBarrierSquare x * A :=
        mul_le_mul (planeBarrierSquare_abs_coordinate x j) (hac j)
          (abs_nonneg _) hp.le
  have hs : x 0 * a x 0 + x 1 * a x 1 ≤ 2 * A * planeBarrierSquare x := by
    linarith [hj 0, hj 1]
  have hm := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ 4 * (planeBarrierSquare x)⁻¹ ^ 3 by positivity)
  have he : planeBarrierSquare x * (planeBarrierSquare x)⁻¹ ^ 3 =
      planeTailProfile x := by
    unfold planeTailProfile
    field_simp [hp.ne']
  rw [planeTailProfile_fderiv]
  calc
    _ = (x 0 * a x 0 + x 1 * a x 1) * (4 * (planeBarrierSquare x)⁻¹ ^ 3) := by ring
    _ ≤ (2 * A * planeBarrierSquare x) * (4 * (planeBarrierSquare x)⁻¹ ^ 3) := hm
    _ = 8 * A * planeTailProfile x := by rw [show
      (2 * A * planeBarrierSquare x) * (4 * (planeBarrierSquare x)⁻¹ ^ 3) =
        8 * A * (planeBarrierSquare x * (planeBarrierSquare x)⁻¹ ^ 3) by ring, he]

theorem planeTailProfile_generator_bound {ν A : ℝ} (hν : 0 ≤ ν) (hA : 0 ≤ A)
    (a : Plane → Plane) (ha : ∀ x, ‖a x‖ ≤ A) (x : Plane) :
    scalarGenerator ν a planeTailProfile x ≤ (24 * ν + 8 * A) * planeTailProfile x := by
  have hl := mul_le_mul_of_nonneg_left (planeTailProfile_laplacian_bound x) hν
  have ha' := planeTailProfile_advection_bound hA a ha x
  unfold scalarGenerator
  nlinarith

end ForcedComputation.VelocityDetector

end

end OAI
