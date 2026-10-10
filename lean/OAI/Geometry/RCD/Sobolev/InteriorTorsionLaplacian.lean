import OAI.Geometry.RCD.Sobolev.EuclideanInteriorTorsion

namespace OAI

/-! # The exact Laplacian of the compact interior torsion test -/

open Set Metric MeasureTheory InnerProductSpace Laplacian
open scoped ContDiff BigOperators
noncomputable section
namespace RegularPointCoordinates

theorem euclideanInteriorTorsion_laplacian {n : ℕ} (R : ℝ) {δ : ℝ} (hδ : 0<δ)
    (x : Euclidean n) :
    (Δ (euclideanInteriorTorsion n R δ)) x=
      (4/δ)*deriv (deriv boundaryTorsionProfile) (euclideanQuadraticDefect n R x/δ)*‖x‖^2-
      2*(n:ℝ)*deriv boundaryTorsionProfile (euclideanQuadraticDefect n R x/δ) := by
  let g := fun z : Euclidean n => δ⁻¹*euclideanQuadraticDefect n R z
  have hg : ContDiff ℝ 2 g := contDiff_const.mul ((euclideanQuadraticDefect_smooth n R).of_le (by simp))
  have hgd (z v : Euclidean n) : fderiv ℝ g z v=
      δ⁻¹*fderiv ℝ (euclideanQuadraticDefect n R) z v := by
    dsimp only [g]
    rw [fderiv_const_mul ((euclideanQuadraticDefect_smooth n R).differentiable (by simp) z)]
    rfl
  have hglap : (Δ g) x=δ⁻¹*(-2*(n:ℝ)) := by
    change (Δ (δ⁻¹ • euclideanQuadraticDefect n R)) x=_
    rw [laplacian_smul δ⁻¹ ((euclideanQuadraticDefect_smooth n R).contDiffAt.of_le (by simp)),
      euclideanQuadraticDefect_laplacian]
    rfl
  have hgg : (∑ i : Fin n, (fderiv ℝ g x (EuclideanSpace.single i 1))^2)=
      (δ⁻¹)^2*(4*‖x‖^2) := by
    simp_rw [hgd,mul_pow]
    rw [← Finset.mul_sum,euclideanQuadraticDefect_gradient_sq]
  have hP : ContDiff ℝ 2 boundaryTorsionProfile := boundaryTorsionProfile_smooth.of_le (by simp)
  have hPG : ContDiff ℝ 2 (fun z => boundaryTorsionProfile (g z)) := by
    simpa only [Function.comp_def] using hP.comp hg
  have heq : euclideanInteriorTorsion n R δ=δ • (fun z => boundaryTorsionProfile (g z)) := by
    funext z
    simp only [euclideanInteriorTorsion,g,div_eq_inv_mul,Pi.smul_apply,smul_eq_mul]
  rw [heq,laplacian_smul δ hPG.contDiffAt,laplacian_scalar_comp hP hg,hgg,hglap]
  simp only [smul_eq_mul,g,div_eq_inv_mul]
  field_simp
  ring

end RegularPointCoordinates

end

end OAI
