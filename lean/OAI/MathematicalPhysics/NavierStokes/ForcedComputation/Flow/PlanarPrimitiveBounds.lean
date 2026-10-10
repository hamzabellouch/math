import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarBranchStages

namespace OAI

/-! Rational Lipschitz bounds for the elementary planar motions. These
bounds control a whole source neighborhood through the finite schedule. -/

noncomputable section
namespace ForcedComputation.PlanarHamiltonian

open ShearFlows Set

def Primitive.growth (p : Primitive) : ℚ :=
  Primitive.casesOn p (fun _ => 1) (fun _ a => 1 + |a|) (fun _ a => 1 + |a|)

theorem Primitive.growth_one_le (p : Primitive) : 1 ≤ p.growth := by
  cases p <;> simp [Primitive.growth]

theorem shearX_sub_bound (a : ℝ) (x y : Plane) :
    ‖shearX a x - shearX a y‖ ≤ (1 + |a|) * ‖x - y‖ := by
  have hx : |x 0 - y 0| ≤ ‖x - y‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) 0
  have hy : |x 1 - y 1| ≤ ‖x - y‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) 1
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))).mpr
  intro j
  fin_cases j
  · change |(x 0 + a * x 1) - (y 0 + a * y 1)| ≤ _
    rw [show (x 0 + a * x 1) - (y 0 + a * y 1) = (x 0 - y 0) + a * (x 1 - y 1) by ring]
    calc
      |(x 0 - y 0) + a * (x 1 - y 1)| ≤ |x 0 - y 0| + |a * (x 1 - y 1)| := abs_add_le _ _
      _ = |x 0 - y 0| + |a| * |x 1 - y 1| := by rw [abs_mul]
      _ ≤ ‖x - y‖ + |a| * ‖x - y‖ := add_le_add hx (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
      _ = (1 + |a|) * ‖x - y‖ := by ring
  · change |x 1 - y 1| ≤ _
    nlinarith [norm_nonneg (x - y), abs_nonneg a]

theorem shearY_sub_bound (a : ℝ) (x y : Plane) :
    ‖shearY a x - shearY a y‖ ≤ (1 + |a|) * ‖x - y‖ := by
  have hx : |x 0 - y 0| ≤ ‖x - y‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) 0
  have hy : |x 1 - y 1| ≤ ‖x - y‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) 1
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))).mpr
  intro j
  fin_cases j
  · change |x 0 - y 0| ≤ _
    nlinarith [norm_nonneg (x - y), abs_nonneg a]
  · change |(x 1 + a * x 0) - (y 1 + a * y 0)| ≤ _
    rw [show (x 1 + a * x 0) - (y 1 + a * y 0) = (x 1 - y 1) + a * (x 0 - y 0) by ring]
    calc
      |(x 1 - y 1) + a * (x 0 - y 0)| ≤ |x 1 - y 1| + |a * (x 0 - y 0)| := abs_add_le _ _
      _ = |x 1 - y 1| + |a| * |x 0 - y 0| := by rw [abs_mul]
      _ ≤ ‖x - y‖ + |a| * ‖x - y‖ := add_le_add hy (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
      _ = (1 + |a|) * ‖x - y‖ := by ring

theorem Primitive.endpoint_sub_bound (p : Primitive) (x y : Plane) :
    ‖p.endpoint x - p.endpoint y‖ ≤ (p.growth : ℝ) * ‖x - y‖ := by
  cases p with
  | translation v =>
      simp [Primitive.endpoint, Primitive.path, translationPath, Primitive.growth]
  | horizontal c a =>
      let c' : Plane := fun j => (c j : ℝ)
      have hd : (x - c') - (y - c') = x - y := by abel
      have h := shearX_sub_bound a (x - c') (y - c')
      rw [hd] at h
      change ‖(c' + shearX (1 * (a : ℝ)) (x - c')) - (c' + shearX (1 * (a : ℝ)) (y - c'))‖ ≤ _
      simp only [one_mul]
      rw [add_sub_add_left_eq_sub]
      simpa only [Primitive.growth, Rat.cast_add, Rat.cast_one, Rat.cast_abs] using h
  | vertical c a =>
      let c' : Plane := fun j => (c j : ℝ)
      have hd : (x - c') - (y - c') = x - y := by abel
      have h := shearY_sub_bound a (x - c') (y - c')
      rw [hd] at h
      change ‖(c' + shearY (1 * (a : ℝ)) (x - c')) - (c' + shearY (1 * (a : ℝ)) (y - c'))‖ ≤ _
      simp only [one_mul]
      rw [add_sub_add_left_eq_sub]
      simpa only [Primitive.growth, Rat.cast_add, Rat.cast_one, Rat.cast_abs] using h

theorem Primitive.path_sub_bound (p : Primitive) (x y : Plane) (θ : ℝ → ℝ) (t : ℝ)
    (hθ : θ t ∈ Icc (0 : ℝ) 1) :
    ‖p.path θ x t - p.path θ y t‖ ≤ (p.growth : ℝ) * ‖x - y‖ := by
  rw [p.path_segment, p.path_segment]
  have he : (x + θ t • (p.endpoint x - x)) - (y + θ t • (p.endpoint y - y)) =
      (1 - θ t) • (x - y) + θ t • (p.endpoint x - p.endpoint y) := by module
  rw [he]
  apply norm_segment_le _ (p.endpoint_sub_bound x y) hθ
  have hg : (1 : ℝ) ≤ p.growth := by exact_mod_cast p.growth_one_le
  nlinarith [norm_nonneg (x - y)]

end ForcedComputation.PlanarHamiltonian

end

end OAI
