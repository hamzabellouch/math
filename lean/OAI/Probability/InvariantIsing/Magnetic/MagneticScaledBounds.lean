import OAI.Probability.InvariantIsing.Magnetic.MagneticScaledInitial
import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabZero

namespace OAI

/-! Uniform coefficient bounds for the actual radially scaled inverse
curvature, including its ordinary zero-exponent Gaussian step. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma closedMagneticScalarCurvature_weighted_second_bound_nonneg (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (p : ℝ × ℝ) :
    |closedMagneticScalarCurvature L hL ζ p * closedMagneticScalarSecond L hL ζ p| ≤
      magneticSlabPotentialCap L ζ := by
  rcases eq_or_lt_of_le hζ with he | hp
  · subst ζ
    by_cases hs : |p.2| < 1
    · simpa only [closedMagneticScalarCurvature, closedMagneticScalarSecond, hs, ite_true] using
        magneticScalarInverse_zero_weighted_second_bound L hL hL1 p.1 p.2
    · simp only [closedMagneticScalarCurvature, closedMagneticScalarSecond, hs, ite_false,
        mul_zero, abs_zero]
      exact add_nonneg (magneticFourthRatioCap_nonneg _) (sq_nonneg _)
  · exact closedMagneticScalarCurvature_weighted_second_bound L hL hL1 hp hζ1 p

lemma magneticScaledClosedCurvature_weighted_second_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1) (α : ℝ≥0)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (p : ℝ × ℝ) :
    |magneticScaledClosedCurvature L hL α ζ p * magneticScaledClosedSecond L hL α ζ p| ≤
      (α : ℝ) ^ 2 * magneticSlabPotentialCap L ζ := by
  have hb := closedMagneticScalarCurvature_weighted_second_bound_nonneg
    (fieldScaleIncrements α L) (fieldScaleIncrements_positive α L hL)
    (fieldScaleIncrements_exponent_le_one α L hL1) hζ hζ1 ((α : ℝ) ^ 2 * p.1, p.2)
  rw [magneticSlabPotentialCap_scale] at hb
  dsimp only [magneticScaledClosedCurvature, magneticScaledClosedSecond]
  rw [show (α : ℝ) * closedMagneticScalarCurvature (fieldScaleIncrements α L)
      (fieldScaleIncrements_positive α L hL) ζ ((α : ℝ) ^ 2 * p.1, p.2) *
      ((α : ℝ) * closedMagneticScalarSecond (fieldScaleIncrements α L)
        (fieldScaleIncrements_positive α L hL) ζ ((α : ℝ) ^ 2 * p.1, p.2)) =
    (α : ℝ) ^ 2 * (closedMagneticScalarCurvature (fieldScaleIncrements α L)
      (fieldScaleIncrements_positive α L hL) ζ ((α : ℝ) ^ 2 * p.1, p.2) *
      closedMagneticScalarSecond (fieldScaleIncrements α L)
        (fieldScaleIncrements_positive α L hL) ζ ((α : ℝ) ^ 2 * p.1, p.2)) by ring,
    abs_mul, abs_of_nonneg (sq_nonneg (α : ℝ))]
  exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)

lemma magneticScaledClosedCurvature_endpoints (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (ζ v : ℝ) :
    magneticScaledClosedCurvature L hL α ζ (v, -1) = 0 ∧
      magneticScaledClosedCurvature L hL α ζ (v, 1) = 0 := by
  obtain ⟨hl, hr⟩ := closedMagneticScalarCurvature_endpoints (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) ζ ((α : ℝ) ^ 2 * v)
  simp only [magneticScaledClosedCurvature, hl, hr, mul_zero, and_self]

end InvariantIsing

end

end OAI
