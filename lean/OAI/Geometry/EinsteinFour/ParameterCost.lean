import OAI.Geometry.EinsteinFour.ProjectionCost
import OAI.Geometry.EinsteinFour.BianchiHessian

namespace OAI

/-! The actual projected weight cost in the three Bianchi parameters. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- The scalar coefficients in equation (19) bound the actual highest
projection of the unsymmetrized weight derivative tensor. -/
theorem highestProjection_parameter_cost (S : Shape) (v : ℝ) (hv : 0 ≤ v)
    (u : Fin 3 → ℝ) (hu : ∑ s, u s = 0) (x y : ℝ)
    (htx : ∀ s, -x ≤ v * S.s s) (huy : ∀ s, -y ≤ u s)
    (hy : 0 ≤ y) (hxy : x + y ≤ 2) (a p k l : Vec) :
    curvaturePairing (fun s => v * S.s s) u
        (highestProjection (weightTensor a (parameters S p k l)))
        (highestProjection (weightTensor a (parameters S p k l))) / 6 ≤
      ‖a‖ ^ 2 *
        (QuarticEnergy.projectionCoefficient v y S.sigma S.rho * ((5 / 3) * ‖p‖ ^ 2) +
          Energy.defectCoefficient v y * ((parameters S p k l).squaredNorm / 6 -
            (5 / 3) * ‖p‖ ^ 2)) := by
  have ht : ∑ s, v * S.s s = 0 := by
    rw [← Finset.mul_sum, S.trace, mul_zero]
  have hcost := highestProjection_weight_cost (fun s => v * S.s s) u ht hu x y
    htx huy hy hxy a (parameters S p k l)
    (parameters_traceFree S p k l) (parameters_bianchi S p k l)
  have hdiv := div_le_div_of_nonneg_right hcost (show (0 : ℝ) ≤ 6 by norm_num)
  have hnorm :
      (‖a‖ ^ 2 * ((7 / 12) * (4 + y) * (parameters S p k l).squaredNorm -
        (5 / 4) * ∑ s, (v * S.s s) * (∑ b, ‖(parameters S p k l).matrix s b‖ ^ 2))) / 6 =
      ‖a‖ ^ 2 * ((7 / 12) * (4 + y) * ((parameters S p k l).squaredNorm / 6) -
        (5 / 4) * curvatureContraction S v (parameters S p k l)) := by
    rw [curvatureContraction_eq_matrix]
    simp only [Fin.sum_univ_three]
    ring
  rw [hnorm] at hdiv
  exact hdiv.trans (mul_le_mul_of_nonneg_left
    (projection_cost_coefficients S hv y p k l) (sq_nonneg ‖a‖))

/-- For `m=M²` and `dm=-(3/4)M(p-q)`, the exact weight factor is `9/64`.
The coefficient keeps its actual sign throughout the division. -/
theorem squared_weight_parameter_cost (S : Shape) (v : ℝ) (hv : 0 ≤ v)
    (u : Fin 3 → ℝ) (hu : ∑ s, u s = 0) (x y M : ℝ) (hM : M ≠ 0)
    (htx : ∀ s, -x ≤ v * S.s s) (huy : ∀ s, -y ≤ u s)
    (hy : 0 ≤ y) (hxy : x + y ≤ 2) (p q k l : Vec) :
    curvaturePairing (fun s => v * S.s s) u
        (highestProjection (weightTensor ((-(3 / 4 : ℝ) * M) • (p - q)) (parameters S p k l)))
        (highestProjection (weightTensor ((-(3 / 4 : ℝ) * M) • (p - q)) (parameters S p k l))) /
          (24 * M ^ 2) ≤
      (9 / 64 : ℝ) * ‖p - q‖ ^ 2 *
        (QuarticEnergy.projectionCoefficient v y S.sigma S.rho * ((5 / 3) * ‖p‖ ^ 2) +
          Energy.defectCoefficient v y * ((parameters S p k l).squaredNorm / 6 -
            (5 / 3) * ‖p‖ ^ 2)) := by
  have hc := highestProjection_parameter_cost S v hv u hu x y htx huy hy hxy
    ((-(3 / 4 : ℝ) * M) • (p - q)) p k l
  have hd := div_le_div_of_nonneg_right hc (show 0 ≤ 4 * M ^ 2 by positivity)
  have hn : ‖(-(3 / 4 : ℝ) * M) • (p - q)‖ ^ 2 =
      (9 / 16 : ℝ) * M ^ 2 * ‖p - q‖ ^ 2 := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hn] at hd
  convert hd using 1 <;> field_simp [hM] <;> ring

end
end PositiveEinsteinFour.HighestHessian

end OAI
