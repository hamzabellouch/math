import OAI.Geometry.RCD.Coordinates.LinearRadialFits
import OAI.Geometry.RCD.Coordinates.RadialFrameChange

namespace OAI

/-! # Rewriting the actual radial affine fits in one centered frame -/

open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

/-- The covector coefficient of a radial fit after changing its input
frame from M to N. -/
def rebasedRadialOperator {n : ℕ} (N M : Euclidean n ≃L[ℝ] Euclidean n)
    (C : Euclidean n →L[ℝ] Euclidean n) : Euclidean n →L[ℝ] Euclidean n :=
  N.symm.toContinuousLinearMap.comp
    (C.comp (M.symm.toContinuousLinearMap.comp N.toContinuousLinearMap))

/-- The two frame factors are the only loss in the near-identity estimate. -/
theorem rebased_radial_operator_bound {n : ℕ}
    (N M : Euclidean n ≃L[ℝ] Euclidean n) (C : Euclidean n →L[ℝ] Euclidean n) :
    ‖rebasedRadialOperator N M C - 1‖ ≤
      ‖N.symm.toContinuousLinearMap.comp M.toContinuousLinearMap‖ *
      ‖M.symm.toContinuousLinearMap.comp C - 1‖ *
      ‖M.symm.toContinuousLinearMap.comp N.toContinuousLinearMap‖ := by
  let P := N.trans M.symm
  have heq : rebasedRadialOperator N M C =
      P.symm.toContinuousLinearMap * (M.symm.toContinuousLinearMap.comp C) * P.toContinuousLinearMap := by
    ext b
    simp only [rebasedRadialOperator, P, ContinuousLinearMap.comp_apply, mul_apply_eq_comp,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [heq]
  exact radial_frame_change_bound P _

/-- The nearby exact frames lose at most a factor two in the actual
radial operator's near-identity error. -/
theorem rebased_radial_operator_bound_two {n : ℕ}
    (N M : Euclidean n ≃L[ℝ] Euclidean n) (C : Euclidean n →L[ℝ] Euclidean n)
    {δ : ℝ}
    (hN : ‖N.symm.toContinuousLinearMap.comp M.toContinuousLinearMap‖ ≤ Real.sqrt 2)
    (hM : ‖M.symm.toContinuousLinearMap.comp N.toContinuousLinearMap‖ ≤ Real.sqrt 2)
    (hC : ‖M.symm.toContinuousLinearMap.comp C - 1‖ ≤ δ) :
    ‖rebasedRadialOperator N M C - 1‖ ≤ 2 * δ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hC
  calc
    _ ≤ ‖N.symm.toContinuousLinearMap.comp M.toContinuousLinearMap‖ *
      ‖M.symm.toContinuousLinearMap.comp C - 1‖ *
      ‖M.symm.toContinuousLinearMap.comp N.toContinuousLinearMap‖ :=
      rebased_radial_operator_bound N M C
    _ ≤ Real.sqrt 2 * δ * Real.sqrt 2 := by gcongr
    _ = 2 * δ := by nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : MeasureTheory.Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Recentering adds exactly the constant determined by the displacement
of the centers. No gradient or value error is introduced by this rewrite. -/
theorem centered_radial_rebase {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (η : SobolevSpace μ hQ)
    (x z : Euclidean n) (N M : Euclidean n ≃L[ℝ] Euclidean n)
    (C : Euclidean n →L[ℝ] Euclidean n) (b : Euclidean n) :
    centeredAffineSobolev μ hQ u η x (C (M.symm (N b))) =
      (centeredSobolevMap μ hQ u η z).comp N.toContinuousLinearMap
        (rebasedRadialOperator N M C b) +
      ⟪z - x, C (M.symm (N b))⟫_ℝ • η := by
  simp only [ContinuousLinearMap.comp_apply, rebasedRadialOperator,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
    centeredSobolevMap_apply, centeredAffineSobolev, inner_sub_left, sub_smul, neg_smul]
  module

end RegularPointCoordinates

end

end OAI
