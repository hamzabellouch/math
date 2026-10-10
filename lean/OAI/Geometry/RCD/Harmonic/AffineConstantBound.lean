import OAI.Geometry.RCD.Harmonic.AffineEvaluation

namespace OAI

/-! # Recovering the constant operator of a centered affine residual -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The published mean-value estimate recovers the constant coefficient
operator because the same harmonic coordinate map vanishes at the center. -/
theorem LocalHarmonicL2MeanValueInput.affine_constant_operator_bound
    {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hinput : LocalHarmonicL2MeanValueInput hX) (hn : 2 ≤ n)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (R : ℝ), 0 < R → -κ ≤ K * R ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (V : X → Euclidean n),
      (∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) (u j)) →
      ContinuousOn V (ball p R) → V p = 0 →
      (∀ j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u j) =ᵐ[
        (hausdorff n X).restrict (ball p R)] fun x => V x j) →
      ∀ η : SobolevSpace (hausdorff n X) hX.quadratic,
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
        (hausdorff n X).restrict (ball p R)] fun _ => (1 : ℝ)) →
      ∀ (A : Euclidean n →L[ℝ] Euclidean n) (c : Euclidean n →L[ℝ] ℝ) (d : ℝ), 0 ≤ d →
      (∀ b, ‖normalizeLocalL2 (hausdorff n X) (ball p R)
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R)
          (c b • η + sobolevColumnMap (hausdorff n X) hX.quadratic u (A b)))‖ ≤ d * ‖b‖) →
      ‖c‖ ≤ C * d := by
  obtain ⟨C, hC, heval⟩ := affine_evaluation_of_mean_value hX hinput hn hκ
  refine ⟨C, hC, ?_⟩
  intro p R hR hcurv u V hu hV hVp hrep η hη A c d hd herror
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by linarith) hd)
  intro b
  have hh := heval p R hR hcurv u V hu hV hrep η hη (c b) (A b)
  simp only [hVp, inner_zero_left, add_zero] at hh
  have hr : SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R)
      (c b • η + sobolevColumnMap (hausdorff n X) hX.quadratic u (A b)) =
      affineCoordinateMap (hausdorff n X) hX.quadratic u (ball p R)
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c b, A b) := by
    rw [map_add, map_smul, restrictLp_eq_one_of_representative _ _ η _ _ hη,
      affineCoordinateMap_apply]
  have hb := herror b
  rw [hr] at hb
  calc
    ‖c b‖ = |c b| := Real.norm_eq_abs _
    _ ≤ C * ‖normalizeLocalL2 (hausdorff n X) (ball p R)
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (affineCoordinateMap (hausdorff n X) hX.quadratic u (ball p R)
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c b, A b))‖ := hh
    _ ≤ C * (d * ‖b‖) := mul_le_mul_of_nonneg_left hb (by linarith)
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
