import OAI.Geometry.RCD.Metric.DistanceSourceBudget

namespace OAI

/-! # Small full-source mass throughout an almost-Euclidean volume regime -/

open Set Metric MeasureTheory
open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

theorem normalized_volume_bounds {n : ℕ} {r omega epsilon V : ℝ}
    (hr : 0 < r) (homega : 0 < omega)
    (h : |V / (omega * r ^ n) - 1| ≤ epsilon) :
    (1 - epsilon) * omega ≤ r ^ (-(n : ℝ)) * V ∧
      r ^ (-(n : ℝ)) * V ≤ (1 + epsilon) * omega := by
  have he : r ^ (-(n : ℝ)) * V = omega * (V / (omega * r ^ n)) := by
    rw [Real.rpow_neg hr.le, Real.rpow_natCast]
    field_simp
  rw [he]
  have hb := abs_le.mp h
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hb.1 homega.le,
    mul_le_mul_of_nonneg_left hb.2 homega.le]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- An actual dyadic distance source has a small total normalized mass
under the same all-scale relative volume bounds used for the heat family. -/
theorem DyadicDistanceSources.almost_euclidean_budget {n : ℕ} {κ r0 omega epsilon : ℝ} {p : X}
    (D : DyadicDistanceSources μ hQ n κ p r0) (hn : 0 < n) (hκ : 0 ≤ κ)
    (homega : 0 < omega) (hepsilon : 0 ≤ epsilon)
    {model : ℝ → ℝ} (hBG : BallVolumeComparison μ model) (hmodel : Continuous model)
    (hmodelpos : ∀ r, 0 < r → 0 < model r)
    (hvolume : ∀ r, 0 < r → r ≤ r0 → |μ.real (ball p r) / (omega * r ^ n) - 1| ≤ epsilon) :
    Summable (normalizedDistanceSourceMass μ hQ D) ∧
      (∑' i, normalizedDistanceSourceMass μ hQ D i) ≤
        2 * (radialCutoffCoefficient (n : ℝ))⁻¹ * epsilon * omega +
          (4 * κ * r0 ^ 2 * ((1 + epsilon) * omega) * (2 : ℝ) ^ (n : ℝ)) * (4 / 3) := by
  have hp (i : ℕ) : (1 - epsilon) * omega ≤ distanceVolumeProfile μ n p r0 i ∧
      distanceVolumeProfile μ n p r0 i ≤ (1 + epsilon) * omega := by
    have hr : 0 < 2 * distanceSourceRadius r0 i :=
      mul_pos (by norm_num) (distanceSourceRadius_pos D.radius_pos i)
    exact normalized_volume_bounds hr homega
      (hvolume _ hr (distanceSourceRadius_outer_le D.radius_pos.le i))
  obtain ⟨hs, hb⟩ := D.mass_budget μ hQ hn hκ (by positivity)
    hBG hmodel hmodelpos (fun i => (hp i).2)
  refine ⟨hs, hb.trans ?_⟩
  have hc : 0 ≤ (radialCutoffCoefficient (n : ℝ))⁻¹ :=
    inv_nonneg.mpr (radialCutoffCoefficient_pos (by exact_mod_cast hn)).le
  have hfirst := mul_le_mul_of_nonneg_left (hp 0).1 hc
  nlinarith

end RegularPointCoordinates

end

end OAI
