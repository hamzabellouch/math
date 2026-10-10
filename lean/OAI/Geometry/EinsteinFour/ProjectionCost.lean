import OAI.Geometry.EinsteinFour.CoupledCasimir
import OAI.Geometry.EinsteinFour.MinusProjectionCost
import OAI.Geometry.EinsteinFour.RealVectorCost

namespace OAI

/-! Domination of the actual highest projection by the real-vector cost. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

private theorem totalPlus_sub (s : Fin 3) (X Y : Hessian) :
    totalPlus s (X - Y) = totalPlus s X - totalPlus s Y := by
  have h : X - Y = X + (-1 : ℝ) • Y := by module
  rw [h, totalPlus_add, totalPlus_smul]
  module

private theorem projected_plus_pairing (s : Fin 3) (W : Hessian) :
    hessianPairing (totalPlus s W) (totalPlus s (highestProjection W)) =
      hessianNormSq (totalPlus s (highestProjection W)) := by
  have hP := highestProjection_condition W
  have hPP := totalPlus_condition s (totalPlus s (highestProjection W))
    (totalPlus_condition s (highestProjection W) hP)
  have h := highestProjection_pairing_right W
    (totalPlus s (totalPlus s (highestProjection W))) hPP
  have h1 := totalPlus_skew s W (totalPlus s (highestProjection W))
  have h2 := totalPlus_skew s (highestProjection W) (totalPlus s (highestProjection W))
  rw [hessianPairing_self] at h2
  linarith

private theorem projection_difference_plus_energy (W : Hessian)
    (hW : (∑ s : Fin 3, hessianNormSq (totalPlus s W)) = 48 * hessianNormSq W) :
    (∑ s : Fin 3, hessianNormSq (totalPlus s (W - highestProjection W))) =
      48 * hessianNormSq (W - highestProjection W) := by
  have hP := totalPlus_energy_of_condition (highestProjection W)
    (highestProjection_condition W)
  have hN := highestProjection_norm_split W
  rw [hessianNormSq_sub] at hN
  simp only [totalPlus_sub, hessianNormSq_sub, projected_plus_pairing]
  simp only [Fin.sum_univ_three] at hW hP ⊢
  nlinarith

private theorem curvaturePairing_sub_self (t u : Fin 3 → ℝ) (X Y : Hessian) :
    curvaturePairing t u (X - Y) (X - Y) =
      curvaturePairing t u X X - 2 * curvaturePairing t u X Y +
        curvaturePairing t u Y Y := by
  have h : X - Y = X + (-1 : ℝ) • Y := by module
  rw [h]
  simp only [curvaturePairing_add_left, curvaturePairing_add_right,
    curvaturePairing_smul_left, curvaturePairing_smul_right]
  rw [curvaturePairing_comm t u Y X]
  ring

/-- Positivity of the orthogonal complement is proved from its actual energy,
so the highest projected cost is dominated without a type-decomposition premise. -/
theorem highestProjection_curvature_le (t u : Fin 3 → ℝ) (x y : ℝ)
    (ht : ∀ s, -x ≤ t s) (hu : ∀ s, -y ≤ u s)
    (hy : 0 ≤ y) (hxy : x + y ≤ 2) (W : Hessian)
    (hW : (∑ s : Fin 3, hessianNormSq (totalPlus s W)) = 48 * hessianNormSq W) :
    curvaturePairing t u (highestProjection W) (highestProjection W) ≤
      curvaturePairing t u W W := by
  have hnonneg := curvaturePairing_nonneg_of_plus_energy t u x y
    (W - highestProjection W) ht hu hy hxy (projection_difference_plus_energy W hW)
  have hm := curvaturePairing_highestProjection t u (highestProjection W) W
    (highestProjection_condition W)
  rw [curvaturePairing_sub_self] at hnonneg
  rw [curvaturePairing_comm t u W (highestProjection W), ← hm] at hnonneg
  linarith


/-- The complete real-vector upper bound for the constructed highest projection. -/
theorem highestProjection_weight_cost (t u : Fin 3 → ℝ)
    (ht : ∑ s, t s = 0) (hu : ∑ s, u s = 0)
    (x y : ℝ) (htx : ∀ s, -x ≤ t s) (huy : ∀ s, -y ≤ u s)
    (hy : 0 ≤ y) (hxy : x + y ≤ 2) (a : Vec) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    curvaturePairing t u (highestProjection (weightTensor a Z))
      (highestProjection (weightTensor a Z)) ≤
        ‖a‖ ^ 2 * ((7 / 12) * (4 + y) * Z.squaredNorm -
          (5 / 4) * ∑ s, t s * (∑ b, ‖Z.matrix s b‖ ^ 2)) := by
  have hp := highestProjection_curvature_le t u x y htx huy hy hxy
    (weightPlusPart a Z) (weightPlusPart_plus_energy a Z hz hb)
  have hproj : highestProjection (weightPlusPart a Z) =
      highestProjection (weightTensor a Z) := by
    rw [weightPlusPart_eq_plusPolynomial, highestProjection_plusPolynomial]
  rw [hproj] at hp
  have hn := weightPlusPart_norm a Z hz hb
  have hc := totalPlus_weightPlusPart_matrixCost t ht a Z hz hb
  have hm := minusDerivativeCurvatureForm_lower u hu y hy huy (weightPlusPart a Z)
  rw [minusDerivativeCurvatureForm_eq u hu, hn] at hm
  have hupper : curvaturePairing t u (weightPlusPart a Z) (weightPlusPart a Z) ≤
      ‖a‖ ^ 2 * ((7 / 12) * (4 + y) * Z.squaredNorm -
        (5 / 4) * ∑ s, t s * (∑ b, ‖Z.matrix s b‖ ^ 2)) := by
    simp only [curvaturePairing, hessianPairing_self, hn]
    nlinarith
  exact hp.trans hupper

end
end PositiveEinsteinFour.HighestHessian

end OAI
