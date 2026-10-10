import OAI.Geometry.RCD.Sobolev.AffineCoefficientEnergy
import OAI.Geometry.RCD.Harmonic.AffineEvaluation

namespace OAI

/-! # Recovering affine operator coefficients from actual local L2 errors -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Exact half-ball normalization recovers the whole linear coefficient
operator from its affine L2 errors, with one constant before all data. -/
theorem LocalHarmonicL2GradientInput.affine_operator_bound
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
      ∀ (A : Euclidean n →L[ℝ] Euclidean n) (c : Euclidean n →L[ℝ] ℝ) (d : ℝ), 0 ≤ d →
      (∀ b, ‖normalizeLocalL2 (hausdorff n X) (ball p R)
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p R)
          (c b • η + sobolevColumnMap (hausdorff n X) hX.quadratic u (A b)))‖ ≤ d * ‖b‖) →
      ‖N.symm.toContinuousLinearMap.comp A‖ ≤ C / R * d := by
  obtain ⟨C, hC, hcoef⟩ := hinput.affine_coefficient hn hκ
  refine ⟨C, hC, ?_⟩
  intro p R hR hcurv u N hN hu η hη A c d hd hbound
  let μ := hausdorff n X
  let hQ := hX.quadratic
  have hηharm := isSobolevHarmonicOn_of_local_constant μ hQ (ball p R) measurableSet_ball η 1 hη
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  change ‖N.symm (A b)‖ ≤ C / R * d * ‖b‖
  let w := c b • η + sobolevColumnMap μ hQ u (A b)
  have hw : IsSobolevHarmonicOn μ hQ (ball p R) w :=
    (hηharm.smul μ hQ (c b)).add μ hQ (IsSobolevHarmonicOn.linearCombination μ hQ hu (A b))
  have hc : SobolevSpace.toLp μ hQ (w - sobolevColumnMap μ hQ u (A b))
      =ᵐ[μ.restrict (ball p R)] fun _ => c b := by
    change SobolevSpace.toLp μ hQ ((c b • η + sobolevColumnMap μ hQ u (A b)) -
      sobolevColumnMap μ hQ u (A b)) =ᵐ[_] _
    rw [add_sub_cancel_right, map_smul]
    filter_upwards [hη, ae_restrict_of_ae (Lp.coeFn_smul (c b) (SobolevSpace.toLp μ hQ η))]
      with x hx hs
    rw [hs]
    change c b * SobolevSpace.toLp μ hQ η x = c b
    rw [show SobolevSpace.toLp μ hQ η x = 1 from hx, mul_one]
  have hk := hcoef p R hR hcurv u N hN (A b) w (c b) hw hc
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hd (norm_nonneg b))).mpr (hbound b)
  have hh := hk.trans (mul_le_mul_of_nonneg_left hs (sq_nonneg (C / R)))
  apply (sq_le_sq₀ (norm_nonneg (N.symm (A b))) (by positivity : 0 ≤ C / R * d * ‖b‖)).mp
  convert hh using 1; ring

end RegularPointCoordinates

end

end OAI
