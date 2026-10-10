import OAI.Geometry.RCD.Harmonic.AffineOperatorBound
import OAI.Geometry.RCD.Coordinates.CovectorCommutator

namespace OAI

/-! # Two-center coefficient recovery from the actual affine L2 residual -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Published harmonic gradient control and exact normalization recover
the difference B of the radial matrices from the affine commutator residual.
The displayed residual is the output of the Sobolev commutator identity. -/
theorem LocalHarmonicL2GradientInput.covector_coefficient_recovery
    {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hinput : LocalHarmonicL2GradientInput hX) (hn : 2 ≤ n)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (R : ℝ), 0 < R → -κ ≤ K * R ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (N : Euclidean n ≃L[ℝ] Euclidean n),
      IsExactMeanNormalization (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u)
        (ball p (R / 2)) measurableSet_ball N →
      (∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) (u j)) →
      ∀ η : SobolevSpace (hausdorff n X) hX.quadratic,
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
        (hausdorff n X).restrict (ball p R)] fun _ => (1 : ℝ)) →
      ∀ (A B : Euclidean n →L[ℝ] Euclidean n) (c : Euclidean n →L[ℝ] ℝ) (d : ℝ), 0 ≤ d →
      ‖A - 1‖ ≤ 1 / 4 →
      (∀ b, ‖normalizeLocalL2 (hausdorff n X) (ball p R)
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R)
          (c b • η + sobolevColumnMap (hausdorff n X) hX.quadratic u ((A * B - B * (A - 1)) b)))‖ ≤ d * ‖b‖) →
      ‖B‖ ≤ 2 * ‖N.toContinuousLinearMap‖ * (C / R * d) := by
  obtain ⟨C, hC, hcoeff⟩ := hinput.affine_operator_bound hn hκ
  refine ⟨C, hC, ?_⟩
  intro p R hR hcurv u N hN hu η hη A B c d hd hA herror
  let T := A * B - B * (A - 1)
  have ht := hcoeff p R hR hcurv u N hN hu η hη T c d hd herror
  have hT : ‖T‖ ≤ ‖N.toContinuousLinearMap‖ * (C / R * d) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro b
    have hh := (N.symm.toContinuousLinearMap.comp T).le_opNorm b
    have hb : ‖N.symm (T b)‖ ≤ (C / R * d) * ‖b‖ :=
      hh.trans (mul_le_mul_of_nonneg_right ht (norm_nonneg b))
    calc
      ‖T b‖ = ‖N (N.symm (T b))‖ := by rw [N.apply_symm_apply]
      _ ≤ ‖N.toContinuousLinearMap‖ * ‖N.symm (T b)‖ := N.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖N.toContinuousLinearMap‖ * ((C / R * d) * ‖b‖) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = _ := by ring
  exact (covector_commutator_norm_le A B hA hT).trans_eq (by ring)

end RegularPointCoordinates

end

end OAI
