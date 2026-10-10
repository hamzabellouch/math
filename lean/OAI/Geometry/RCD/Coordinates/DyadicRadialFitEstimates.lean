import OAI.Geometry.RCD.Coordinates.DyadicRadialFit
import OAI.Geometry.RCD.Coordinates.FramedDyadicFit
import OAI.Geometry.RCD.Coordinates.NormalizedFrameRadialSmallness

namespace OAI

/-! # Estimates for one canonical dyadic radial-fit sequence -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

def radialFitStepConstant (K : ℝ) (n : ℕ) (A B J Cχ : ℝ) (m : ℕ) : ℝ :=
  let θ := (1 / 2 : ℝ) ^ m
  (64 / θ) * (Real.sqrt ((5 / 3 : ℝ) * (θ ^ n)⁻¹) + (1 / 2 : ℝ) * θ * Real.sqrt θ) *
    Real.sqrt ((n : ℝ) * radialCorrectionConstant K n 1 A B J Cχ *
      ((4 / (3 * euclideanUnitVolume n)) * (64 : ℝ) ^ n))

def radialFitQualitativeConstant (n : ℕ) (Cχ : ℝ) : ℝ :=
  ((n : ℝ) * (1000 * ((n : ℝ) + 1) ^ 2 * (Cχ + 1))) *
    radialNormalizationRestrictionConstant n * ((5 / 3 : ℝ) * (4 : ℝ) ^ n)

theorem radialFitStepConstant_nonneg (K : ℝ) (n : ℕ) (A B J Cχ : ℝ) (m : ℕ) :
    0 ≤ radialFitStepConstant K n A B J Cχ m := by
  dsimp only [radialFitStepConstant]
  positivity

theorem radialFitQualitativeConstant_nonneg (n : ℕ) {Cχ : ℝ} (hCχ : 0 ≤ Cχ) :
    0 ≤ radialFitQualitativeConstant n Cχ := by
  have hd := zero_le_one.trans (radialNormalizationRestrictionConstant_ge_one n)
  dsimp only [radialFitQualitativeConstant]
  positivity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  [IsFiniteMeasureOnCompacts (hausdorff n X)]
  {κ r0 B J C A Cχ L : ℝ} {p : X}
  {S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0}
  (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C)
  (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
  (hbase : ∀ i j, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 64)),
    localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ L ^ 2)

theorem dyadicRadialFit_step
    (hn : 2 ≤ n) (hhessian : LocalPoissonHessianInput hX)
    (hκ : 0 ≤ κ) (hK : -κ ≤ K) (hB : 0 ≤ B) (hJ : 0 ≤ J) (hA : 0 ≤ A) (hCχ : 0 ≤ Cχ)
    (i : ℕ) (hs1 : distanceSourceRadius r0 i ≤ 1)
    (F : Euclidean n ≃L[ℝ] Euclidean n)
    (hu : ∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball p (distanceSourceRadius r0 i / 4)) (transformedColumn (hausdorff n X) hX.quadratic u F j))
    (hgrad : ∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic
        (transformedColumn (hausdorff n X) hX.quadratic u F j)
        (transformedColumn (hausdorff n X) hX.quadratic u F j) x ≤ (1 + (1 : ℝ)) ^ 2)
    (hf : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T.replacement i) (T.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (distanceSourceRadius r0 i / 64) Cχ)
    (hvol : 0 < (hausdorff n X).real (ball p (distanceSourceRadius r0 i / 64)))
    (hdouble : 2 * (hausdorff n X).real (ball p (distanceSourceRadius r0 i / 64)) ≤
      (hausdorff n X).real (ball p (2 * (distanceSourceRadius r0 i / 64))))
    (m : ℕ)
    (hfit : HasNormalizedAffineImprovement hX u p (distanceSourceRadius r0 i / 64) ((1 / 2 : ℝ) ^ m))
    (hquarter : ∀ t : ℝ, 0 < t → t ≤ distanceSourceRadius r0 i →
      |(hausdorff n X).real (ball p t) / (euclideanUnitVolume n * t ^ n) - 1| ≤ 1 / 4)
    (b : Euclidean n) :
    dyadicRadialFit hX T u L hbase (i + m) b ≤
      (1 / 2 : ℝ) * Real.sqrt ((1 / 2 : ℝ) ^ m) * dyadicRadialFit hX T u L hbase i b +
      radialFitStepConstant K n A B J Cχ m * ‖F.symm b‖ *
        Real.sqrt (normalizedPoissonDefect (hausdorff n X) hX.quadratic S i) := by
  have hstep := actual_framed_dyadic_radial_fit hX hn hhessian hκ hK hB hJ hA
    (by norm_num : (0 : ℝ) ≤ 1) hCχ p S T i hs1 u F hu hgrad (hbase i)
    hf χ hvol hdouble m hfit hquarter
  dsimp only at hstep
  have hb := hstep b
  convert hb using 1
  · symm
    apply radialFitError_radius_eq
    exact (distanceSourceRadius_testing_shift r0 i m).symm
  · dsimp only [dyadicRadialFit, radialFitStepConstant]
    ring

theorem dyadicRadialFit_smallness {δ : ℝ} (hδ : 0 ≤ δ)
    (hδ1 : radialNormalizationRestrictionConstant n * δ ≤ 1) (hCχ : 0 ≤ Cχ)
    (i : ℕ) (F : Euclidean n ≃L[ℝ] Euclidean n) (v : X → Euclidean n)
    (hfirst : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2 * distanceSourceRadius r0 i) δ
      (transformedColumn (hausdorff n X) hX.quadratic u F) v)
    (hmetric : IsPointedApproximation p 0 (distanceSourceRadius r0 i / 64) 4 δ
      (fun x => (distanceSourceRadius r0 i / 64)⁻¹ • (v x - v p)))
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p (distanceSourceRadius r0 i / 64) Cχ)
    (hquarter : ∀ t : ℝ, 0 < t → t ≤ 2 * distanceSourceRadius r0 i →
      |(hausdorff n X).real (ball p t) / (euclideanUnitVolume n * t ^ n) - 1| ≤ 1 / 4)
    (b : Euclidean n) :
    (dyadicRadialFit hX T u L hbase i b) ^ 2 ≤
      radialFitQualitativeConstant n Cχ * δ * ‖F.symm b‖ ^ 2 := by
  exact T.normalized_frame_fit_smallness (hausdorff n X) hX.quadratic i
    (euclideanUnitVolume_pos n) hδ hδ1 hCχ hquarter u F v hfirst hmetric χ b
    (gamma_column_le_of_diagonal_bounds (hausdorff n X) hX.quadratic u _ L (hbase i) b)

end RegularPointCoordinates

end

end OAI
