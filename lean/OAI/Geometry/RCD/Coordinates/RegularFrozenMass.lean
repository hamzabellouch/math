import OAI.Geometry.RCD.Coordinates.RegularPatchHeatComparison
import OAI.Geometry.RCD.Coordinates.RegularShiftedNormalizationSum

namespace OAI

/-! # Small full-mass operators in the constructed frozen heat frames -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The two-step interior shift only increases the inverse metric, so the
actual patch mass remains small in the chosen frozen frame. -/
theorem regular_patch_mass_frozen_small {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q z : X} (hq : q ∈ ball base (e.heat.radius / 32))
    (hz : z ∈ ball base (e.heat.radius / 32))
    (hzeta : 0 ≤ zeta) (hzeta1 : zeta ≤ 1) (hCχ : 0 ≤ Cχ)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 2)
    (hnear : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 64 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (i : ℕ)
    (hroom : dist z q ≤ 32 * (e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15)))
    (xi : Euclidean n) :
    let r := e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15)
    ⟪xi, e.heat.pinchingMassMatrix z hz (e.heat.shift + i) xi⟫_ℝ ≤
      (4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
        (zeta + |K| * r ^ 2)) * ‖e.heat.frozenAt q i xi‖ ^ 2 := by
  intro r
  have hm := regular_patch_mass_small hX e hq hz hzeta hzeta1 hCχ hsmall hnear
    (e.heat.shift + i) (by omega) hroom xi
  have h := (inverse_increment_isPositive _ _
    (e.heat.heatAt_isPositive q (e.heat.shift + i + 15))
    (e.heat.heatAt_isPositive q (e.heat.shift + i + 15 + 2))
    (e.heat.heatAt_two_step_decrement_positive hq (e.heat.shift + i + 15) (by omega))).inner_nonneg_right xi
  simp only [sub_apply, inner_sub_right, ContinuousLinearEquiv.coe_coe] at h
  have hmetric : ⟪xi, (e.heat.heatAt q (e.heat.shift + i + 15)).symm xi⟫_ℝ ≤
      ‖e.heat.frozenAt q i xi‖ ^ 2 := by
    rw [e.heat.frozenAt_norm_sq]
    rw [show e.heat.shift + i + 15 + 2 = e.heat.shift + i + 17 by omega] at h
    linarith only [h]
  have hc : 0 ≤ 4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
      (zeta + |K| * r ^ 2) := by
    have homega : 0 < euclideanUnitVolume n := euclideanUnitVolume_pos n
    dsimp only [pinchingMassUnitFactor, regularSmallMassCoefficient]
    positivity
  exact hm.trans (mul_le_mul_of_nonneg_left hmetric hc)

/-- A finite family incurs exactly its overlap multiplicity in the
pointwise mass bound; the full net cardinality never enters it. -/
theorem regular_patch_mass_sum_frozen_small {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    {q : X} (hq : q ∈ ball base (e.heat.radius / 32))
    (hzeta : 0 ≤ zeta) (hzeta1 : zeta ≤ 1) (hCχ : 0 ≤ Cχ)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 8 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 2)
    (hnear : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 64 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    {ι : Type*} (s : Finset ι)
    (centers : ι → {z : X // z ∈ ball base (e.heat.radius / 32)})
    {N : ℕ} (hcard : s.card ≤ N) (i : ℕ)
    (hroom : ∀ y ∈ s, dist (centers y).val q ≤
      32 * (e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15)))
    (xi : Euclidean n) :
    let r := e.heat.radius / (2 : ℝ) ^ (e.heat.shift + i + 15)
    (∑ y ∈ s, ⟪xi, e.heat.pinchingMassMatrix (centers y).val (centers y).property
      (e.heat.shift + i) xi⟫_ℝ) ≤
      (N : ℝ) * (4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
        (zeta + |K| * r ^ 2)) * ‖e.heat.frozenAt q i xi‖ ^ 2 := by
  intro r
  have hc : 0 ≤ (4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
      (zeta + |K| * r ^ 2)) * ‖e.heat.frozenAt q i xi‖ ^ 2 := by
    have homega : 0 < euclideanUnitVolume n := euclideanUnitVolume_pos n
    dsimp only [pinchingMassUnitFactor, regularSmallMassCoefficient]
    positivity
  calc
    _ ≤ ∑ _y ∈ s, (4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
        (zeta + |K| * r ^ 2)) * ‖e.heat.frozenAt q i xi‖ ^ 2 :=
      Finset.sum_le_sum (fun y hy => regular_patch_mass_frozen_small hX e hq
        (centers y).property hzeta hzeta1 hCχ hsmall hnear i (hroom y hy) xi)
    _ = (s.card : ℝ) * ((4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
        (zeta + |K| * r ^ 2)) * ‖e.heat.frozenAt q i xi‖ ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * ((4 * pinchingMassUnitFactor n * regularSmallMassCoefficient n Cχ *
        (zeta + |K| * r ^ 2)) * ‖e.heat.frozenAt q i xi‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
