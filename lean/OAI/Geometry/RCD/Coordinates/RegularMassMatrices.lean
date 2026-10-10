import OAI.Geometry.RCD.Coordinates.RegularMeanPinching

namespace OAI

/-! # Canonical mean and local mass matrices of the constructed neighborhood -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

namespace RegularBilinearData

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
  {base : X} {ker : ℝ → X → X → ℝ}
  {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker} {enlargement zeta : ℝ}
  (d : RegularBilinearData hX base hk enlargement zeta)
  (q : X) (hq : q ∈ ball base (d.radius / 32))

/-- The actual dyadic mean Gram, using an already constructed exact frame
only to certify its invertibility. -/
def meanAt (i : ℕ) : Euclidean n ≃L[ℝ] Euclidean n :=
  meanGramEquiv (hausdorff n X) hX.quadratic
    (sobolevColumnMap (hausdorff n X) hX.quadratic d.coordinates)
    (ball q (d.radius / 2 ^ i)) measurableSet_ball
    (Classical.choose (d.localData q hq).2.2.2 i)
    ((Classical.choose_spec (d.localData q hq).2.2.2).1 i)

theorem meanAt_toContinuousLinearMap (i : ℕ) :
    (d.meanAt q hq i).toContinuousLinearMap =
      sobolevMeanGram (hausdorff n X) hX.quadratic
        (sobolevColumnMap (hausdorff n X) hX.quadratic d.coordinates)
        (ball q (d.radius / 2 ^ i)) measurableSet_ball := by
  ext v
  rfl

theorem meanAt_isPositive (i : ℕ) : (d.meanAt q hq i).toContinuousLinearMap.IsPositive := by
  rw [meanAt_toContinuousLinearMap]
  exact sobolevMeanGram_isPositive _ _ _ _ _

/-- These matrices retain the full original Bochner measure and use the
mean at a fixed dyadic offset. Their mass radius is one third of that mean radius. -/
def pinchingMassMatrix (i : ℕ) : Euclidean n →L[ℝ] Euclidean n :=
  let s := distanceSourceRadius d.radius i
  frozenConjugate (d.meanAt q hq (i + 15))
    ((s ^ 2 / s ^ n) • d.mass.massOperator (ball q (s / 49152)))

theorem pinchingMassMatrix_isPositive (i : ℕ) : (d.pinchingMassMatrix q hq i).IsPositive := by
  apply frozenConjugate_isPositive
  apply ContinuousLinearMap.IsPositive.smul_of_nonneg
  · exact d.mass.massOperator_isPositive _ measurableSet_ball
  · have hs := distanceSourceRadius_pos d.radius_pos i
    positivity

end RegularBilinearData

/-- The matrix furnished by the pinching proof equals the canonical mean
matrix at the shifted dyadic index. This identification uses equality of
operators, without comparing or commuting arbitrary normalization frames. -/
theorem regular_pinching_matrix_identification {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
    {base : X} {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker} {enlargement zeta : ℝ}
    (d : RegularBilinearData hX base hk enlargement zeta)
    (q : X) (hq : q ∈ ball base (d.radius / 32)) (i : ℕ)
    (R : Euclidean n ≃L[ℝ] Euclidean n)
    (hR : R.toContinuousLinearMap = sobolevMeanGram (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic d.coordinates)
      (ball q (3 * (distanceSourceRadius d.radius i / 49152))) measurableSet_ball) :
    R = d.meanAt q hq (i + 15) := by
  apply DFunLike.ext
  intro v
  have hcanonical := d.meanAt_toContinuousLinearMap q hq (i + 15)
  rw [← pinching_mean_radius] at hcanonical
  exact congrArg (fun T : Euclidean n →L[ℝ] Euclidean n => T v) (hR.trans hcanonical.symm)

end RegularPointCoordinates

end

end OAI
