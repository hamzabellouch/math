import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneTailProfile

namespace OAI

/-! The rational scalar tail changes by only a fixed factor on a unit
coordinate neighborhood. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows

theorem planeBarrierSquare_near {x y : Plane} (hxy : ∀ j, |x j - y j| ≤ 1) :
    planeBarrierSquare x ≤ 5 * planeBarrierSquare y := by
  have hj (j : Fin 2) : (x j) ^ 2 ≤ 2 * (y j) ^ 2 + 2 := by
    have hd : (x j - y j) ^ 2 ≤ 1 := by
      nlinarith [(abs_le.mp (hxy j)).1, (abs_le.mp (hxy j)).2,
        sq_nonneg (x j - y j)]
    nlinarith [sq_nonneg (x j - 2 * y j)]
  have h0 := hj 0
  have h1 := hj 1
  unfold planeBarrierSquare
  nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]

theorem planeTailProfile_near {x y : Plane} (hxy : ∀ j, |x j - y j| ≤ 1) :
    planeTailProfile y ≤ 25 * planeTailProfile x := by
  have hx := planeBarrierSquare_pos x
  have hy := planeBarrierSquare_pos y
  have hb := planeBarrierSquare_near hxy
  have he : planeBarrierSquare x ^ 2 ≤ 25 * planeBarrierSquare y ^ 2 := by
    nlinarith [sq_nonneg (5 * planeBarrierSquare y - planeBarrierSquare x)]
  have hd : (1 : ℝ) / planeBarrierSquare y ^ 2 ≤ 25 / planeBarrierSquare x ^ 2 :=
    (div_le_div_iff₀ (sq_pos_of_pos hy) (sq_pos_of_pos hx)).mpr (by simpa using he)
  simpa only [planeTailProfile, one_div, div_eq_mul_inv, inv_pow, one_mul] using hd

theorem planeTailProfile_line_le (x v : Plane) {t : ℝ} (ht : |t| ≤ 1)
    (hv : ‖v‖ ≤ 1) : planeTailProfile (x + t • v) ≤ 25 * planeTailProfile x := by
  apply planeTailProfile_near
  intro j
  have hvj : |v j| ≤ 1 :=
    (show |v j| ≤ ‖v‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j).trans hv
  have hp := mul_le_mul ht hvj (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  change |x j - (x j + t * v j)| ≤ 1
  rw [show x j - (x j + t * v j) = -(t * v j) from by ring, abs_neg, abs_mul]
  simpa only [one_mul] using hp

end ForcedComputation.VelocityDetector

end

end OAI
