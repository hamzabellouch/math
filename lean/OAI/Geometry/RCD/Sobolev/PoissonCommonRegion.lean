import OAI.Geometry.RCD.Harmonic.DyadicDistanceReplacements
import OAI.Geometry.RCD.Sobolev.PoissonGradientBridge

namespace OAI

/-! # Common-region data for actual two-center replacements -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- The actual replacement has a global value bound in its natural squared
length units; it follows from the positive datum and the proved height. -/
theorem DyadicDistanceReplacements.value_bound {n : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ) :
    ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (T.replacement i) x| ≤
      max 8 B * (distanceSourceRadius r0 i) ^ 2 := by
  let r := distanceSourceRadius r0 i
  have hr : 0 < r := distanceSourceRadius_pos S.radius_pos i
  let q := positiveSquaredDistance μ hQ (by positivity : 0 ≤ 4 * r) (T.cutoff i)
  have hqrep := positiveSquaredDistance_representative μ hQ (by positivity : 0 ≤ 4 * r) (T.cutoff i)
  filter_upwards [hqrep, T.height i,
    Lp.coeFn_sub (SobolevSpace.toLp μ hQ q) (SobolevSpace.toLp μ hQ (T.replacement i))]
    with x hqx hh hsub
  have hqbound := positiveSquaredDistanceValue_bounds μ hQ (by positivity : 0 ≤ 4 * r) (T.cutoff i) x
  have hq0 : 0 ≤ SobolevSpace.toLp μ hQ q x := by rw [hqx]; exact hqbound.1
  have hq8 : SobolevSpace.toLp μ hQ q x ≤ 8 * r ^ 2 := by
    rw [hqx]
    nlinarith [hqbound.2]
  change 0 ≤ SobolevSpace.toLp μ hQ (q - T.replacement i) x ∧
    SobolevSpace.toLp μ hQ (q - T.replacement i) x ≤ B * r ^ 2 at hh
  rw [map_sub, hsub, Pi.sub_apply] at hh
  have h8 := mul_le_mul_of_nonneg_right (le_max_left 8 B) (sq_nonneg r)
  have hB := mul_le_mul_of_nonneg_right (le_max_right 8 B) (sq_nonneg r)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Equal Laplacians remain equal on a smaller ball around another center. -/
theorem DyadicDistanceReplacements.laplacian_on_ball {n : ℕ} {κ r0 B J C : ℝ} {p : X}
    {S : DyadicDistanceSources μ hQ n κ p r0}
    (T : DyadicDistanceReplacements μ hQ S B J C) (i : ℕ)
    (z : X) {R : ℝ} (hroom : R + dist z p ≤ distanceSourceRadius r0 i) :
    IsConstantLaplacianOn μ hQ (ball z R) (T.replacement i)
      ((n : ℝ) + κ * (4 * distanceSourceRadius r0 i) ^ 2) :=
  (T.laplacian i).mono μ hQ measurableSet_ball (ball_subset_ball' hroom)

/-- The harmonic difference in the two-center argument is constructed
from the actual same-scale replacements and their common constant source. -/
theorem common_replacement_difference_harmonic
    {n : ℕ} {κ r0 B₁ J₁ C₁ B₂ J₂ C₂ : ℝ} {p₁ p₂ : X}
    {S₁ : DyadicDistanceSources μ hQ n κ p₁ r0}
    {S₂ : DyadicDistanceSources μ hQ n κ p₂ r0}
    (T₁ : DyadicDistanceReplacements μ hQ S₁ B₁ J₁ C₁)
    (T₂ : DyadicDistanceReplacements μ hQ S₂ B₂ J₂ C₂)
    (i : ℕ) (z : X) {R : ℝ}
    (hroom₁ : R + dist z p₁ ≤ distanceSourceRadius r0 i)
    (hroom₂ : R + dist z p₂ ≤ distanceSourceRadius r0 i) :
    IsSobolevHarmonicOn μ hQ (ball z R) (T₂.replacement i - T₁.replacement i) :=
  (T₂.laplacian_on_ball μ hQ i z hroom₂).sub_harmonic μ hQ
    (T₁.laplacian_on_ball μ hQ i z hroom₁)

end RegularPointCoordinates

end

end OAI
