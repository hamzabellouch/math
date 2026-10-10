import OAI.Geometry.RCD.Harmonic.AffineConstantBound
import OAI.Geometry.RCD.Coordinates.CovectorCoefficientRecovery

namespace OAI

/-! # Recovering both coefficients of the two-center commutator residual -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Exact normalization and the two published harmonic interior estimates
recover the matrix difference and constant term from the SAME residual. -/
theorem two_center_affine_recovery {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hgradient : LocalHarmonicL2GradientInput hX)
    (hmean : LocalHarmonicL2MeanValueInput hX) (hn : 2 ≤ n)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ Cg Cm : ℝ, 1 ≤ Cg ∧ 1 ≤ Cm ∧
      ∀ (p : X) (R : ℝ), 0 < R → -κ ≤ K * R ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (V : X → Euclidean n) (N : Euclidean n ≃L[ℝ] Euclidean n),
      IsExactMeanNormalization (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic u)
        (ball p (R / 2)) measurableSet_ball N →
      (∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) (u j)) →
      ContinuousOn V (ball p R) → V p = 0 →
      (∀ j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u j) =ᵐ[
        (hausdorff n X).restrict (ball p R)] fun x => V x j) →
      ∀ η : SobolevSpace (hausdorff n X) hX.quadratic,
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
        (hausdorff n X).restrict (ball p R)] fun _ => (1 : ℝ)) →
      ∀ (A B : Euclidean n →L[ℝ] Euclidean n) (c : Euclidean n →L[ℝ] ℝ) (d : ℝ),
      0 ≤ d → ‖A - 1‖ ≤ 1 / 4 →
      (∀ b, ‖normalizeLocalL2 (hausdorff n X) (ball p R)
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R)
          (sobolevColumnMap (hausdorff n X) hX.quadratic u ((A * B - B * (A - 1)) b) -
            c ((A - 1) b) • η))‖ ≤ d * ‖b‖) →
      ‖B‖ ≤ 2 * ‖N.toContinuousLinearMap‖ * (Cg / R * d) ∧
        ‖c.comp (A - 1)‖ ≤ Cm * d := by
  obtain ⟨Cg, hCg, hcoeff⟩ := hgradient.covector_coefficient_recovery hn hκ
  obtain ⟨Cm, hCm, hconst⟩ := hmean.affine_constant_operator_bound hn hκ
  refine ⟨Cg, Cm, hCg, hCm, ?_⟩
  intro p R hR hcurv u V N hN hu hV hVp hrep η hη A B c d hd hA herror
  let T := A * B - B * (A - 1)
  let c' := -(c.comp (A - 1))
  have he (b) : c' b • η + sobolevColumnMap (hausdorff n X) hX.quadratic u (T b) =
      sobolevColumnMap (hausdorff n X) hX.quadratic u (T b) - c ((A - 1) b) • η := by
    simp only [c', neg_apply, ContinuousLinearMap.comp_apply, neg_smul]
    module
  have herr (b) : ‖normalizeLocalL2 (hausdorff n X) (ball p R)
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R)
        (c' b • η + sobolevColumnMap (hausdorff n X) hX.quadratic u (T b)))‖ ≤ d * ‖b‖ := by
    rw [he]
    exact herror b
  refine ⟨hcoeff p R hR hcurv u N hN hu η hη A B c' d hd hA herr, ?_⟩
  have hc := hconst p R hR hcurv u V hu hV hVp hrep η hη T c' d hd herr
  simpa only [c', norm_neg] using hc

end RegularPointCoordinates

end

end OAI
