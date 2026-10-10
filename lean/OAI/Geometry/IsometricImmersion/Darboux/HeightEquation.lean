import OAI.Geometry.IsometricImmersion.Curvature.GaussEquation
import OAI.Geometry.IsometricImmersion.Immersions.HeightNorm
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
open scoped ContDiff BigOperators
namespace SmoothLocal.Geometry

theorem exists_isUnitNormalAt {g : MetricField} {F : Coord → Ambient} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    {p : Coord} (hp : p ∈ U) : ∃ n, IsUnitNormalAt F n p := by
  obtain ⟨n, hn, hnt⟩ := exists_unit_normal_of_independent_tangents
    (fun i => coordPartial i F p) (isometric_tangents_independent hg hF hp)
  refine ⟨n, hn, ?_⟩
  intro v
  rw [← Finset.univ_sum_single v, map_sum, sum_inner]
  apply Finset.sum_eq_zero
  intro i _
  have hsingle : Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
    ext j
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hsingle, map_smul, real_inner_smul_left]
  change v i * inner ℝ (coordPartial i F p) n = 0
  rw [hnt, mul_zero]

theorem geometric_height_equation {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hF : IsometricOn g F U)
    (hU : IsOpen U) (e : Ambient) (he : inner ℝ e e = 1)
    {p : Coord} (hp : p ∈ U) :
    (covHessian g (height F e) p).det =
      gaussianCurvature g p * (g p).det * (1 - covectorNormSq g (height F e) p) := by
  obtain ⟨n, hn⟩ := exists_isUnitNormalAt hg hF hp
  have hnorm := height_normal_tangent_norm hg hF hU hp hn e
  have hnu : (inner ℝ n e) ^ 2 = 1 - covectorNormSq g (height F e) p := by
    rw [he] at hnorm
    linarith
  rw [covHessian_height_eq_normal_mul_secondFundamental hg hF hU hp hn e,
    SmoothLocal.det_two_smul,
    det_secondFundamental_eq_gaussianCurvature_mul_det hg hF hU hp hn, hnu]
  ring

theorem geometric_height_normal_point {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hF : IsometricOn g F U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {e : Ambient} (he : IsUnitNormalAt F e p) :
    fderiv ℝ (height F e) p = 0 ∧
      covHessian g (height F e) p = secondFundamental F e p :=
  ⟨height_derivative_at_normal hF.1 hU hp he,
    covHessian_height_at_normal g hF.1 hU hp he⟩

end SmoothLocal.Geometry

end

end OAI
