import OAI.Geometry.RCD.Metric.DyadicDistanceSources
import OAI.Geometry.RCD.Harmonic.RadialDyadicBudget
import OAI.Geometry.RCD.Metric.BoundedVolumeBudget

namespace OAI

/-! # Summability of the constructed distance sources from volume bounds -/

open Set Metric MeasureTheory
open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

def distanceVolumeProfile (n : ℕ) (p : X) (r0 : ℝ) (i : ℕ) : ℝ :=
  (2 * distanceSourceRadius r0 i) ^ (-(n : ℝ)) * μ.real (ball p (2 * distanceSourceRadius r0 i))

def normalizedDistanceSourceMass {n : ℕ} {κ r0 : ℝ} {p : X}
    (D : DyadicDistanceSources μ hQ n κ p r0) (i : ℕ) : ℝ :=
  (distanceSourceRadius r0 i) ^ (-(n : ℝ)) * (D.source i).real (ball p (distanceSourceRadius r0 i))

omit [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
theorem distanceVolumeProfile_succ (n : ℕ) (p : X) (r0 : ℝ) (i : ℕ) :
    distanceVolumeProfile μ n p r0 (i + 1) =
      (distanceSourceRadius r0 i) ^ (-(n : ℝ)) * μ.real (ball p (distanceSourceRadius r0 i)) := by
  unfold distanceVolumeProfile
  rw [distanceSourceRadius_succ, show 2 * (distanceSourceRadius r0 i / 2) =
    distanceSourceRadius r0 i by ring]

theorem DyadicDistanceSources.normalized_mass_le {n : ℕ} {κ r0 C : ℝ} {p : X}
    (D : DyadicDistanceSources μ hQ n κ p r0) (hn : 0 < n) (hκ : 0 ≤ κ)
    {model : ℝ → ℝ} (hBG : BallVolumeComparison μ model) (hmodel : Continuous model)
    (hmodelpos : ∀ r, 0 < r → 0 < model r)
    (hvol : ∀ i, μ.real (ball p (2 * distanceSourceRadius r0 i)) ≤
      C * (2 * distanceSourceRadius r0 i) ^ (n : ℝ)) (i : ℕ) :
    normalizedDistanceSourceMass μ hQ D i ≤ (radialCutoffCoefficient (n : ℝ))⁻¹ *
      (distanceVolumeProfile μ n p r0 (i + 1) - distanceVolumeProfile μ n p r0 i) +
      (4 * κ * r0 ^ 2 * C * (2 : ℝ) ^ (n : ℝ)) * (1 / 4 : ℝ) ^ i := by
  have hr := distanceSourceRadius_pos D.radius_pos i
  have hb := radial_mass_normalized_le (by exact_mod_cast hn) hr
    (by positivity : 0 ≤ κ * (4 * distanceSourceRadius r0 i) ^ 2) (hvol i)
    (D.mass_le μ hQ hn hκ hBG hmodel hmodelpos i)
  rw [distanceVolumeProfile_succ]
  change (distanceSourceRadius r0 i) ^ (-(n : ℝ)) * (D.source i).real
    (ball p (distanceSourceRadius r0 i)) ≤ _
  refine hb.trans_eq ?_
  dsimp only [distanceVolumeProfile]
  rw [distanceSourceRadius_four_sq]
  ring

/-- The full source masses are summable even when the raw Euclidean
volume profile is not monotone. The only volume input is its upper bound. -/
theorem DyadicDistanceSources.mass_budget {n : ℕ} {κ r0 C : ℝ} {p : X}
    (D : DyadicDistanceSources μ hQ n κ p r0) (hn : 0 < n) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    {model : ℝ → ℝ} (hBG : BallVolumeComparison μ model) (hmodel : Continuous model)
    (hmodelpos : ∀ r, 0 < r → 0 < model r)
    (hupper : ∀ i, distanceVolumeProfile μ n p r0 i ≤ C) :
    Summable (normalizedDistanceSourceMass μ hQ D) ∧
      (∑' i, normalizedDistanceSourceMass μ hQ D i) ≤
        (radialCutoffCoefficient (n : ℝ))⁻¹ * (C - distanceVolumeProfile μ n p r0 0) +
          (4 * κ * r0 ^ 2 * C * (2 : ℝ) ^ (n : ℝ)) * (4 / 3) := by
  have hvol (i : ℕ) : μ.real (ball p (2 * distanceSourceRadius r0 i)) ≤
      C * (2 * distanceSourceRadius r0 i) ^ (n : ℝ) := by
    have hp : 0 < (2 * distanceSourceRadius r0 i) ^ (n : ℝ) :=
      Real.rpow_pos_of_pos (by have := distanceSourceRadius_pos D.radius_pos i; positivity) _
    have hi := hupper i
    change (2 * distanceSourceRadius r0 i) ^ (-(n : ℝ)) * _ ≤ C at hi
    rw [Real.rpow_neg (by have := distanceSourceRadius_pos D.radius_pos i; positivity)] at hi
    have hh := mul_le_mul_of_nonneg_left hi hp.le
    simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hp), one_mul, mul_comm] using hh
  apply volume_defect_budget_of_uniform_upper
    (inv_nonneg.mpr (radialCutoffCoefficient_pos (by exact_mod_cast hn)).le)
    (by positivity) hupper
  · intro i
    exact mul_nonneg (Real.rpow_nonneg (distanceSourceRadius_pos D.radius_pos i).le _) ENNReal.toReal_nonneg
  · exact D.normalized_mass_le μ hQ hn hκ hBG hmodel hmodelpos hvol

end RegularPointCoordinates

end

end OAI
