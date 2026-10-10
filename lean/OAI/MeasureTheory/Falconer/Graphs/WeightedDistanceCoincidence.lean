import OAI.MeasureTheory.Falconer.Fourier.WeightedDistanceFourier
import OAI.MeasureTheory.Falconer.Geometry.PositiveDistanceBins

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem weighted_lower_constant_sq (d : PositiveDistanceData) :
    (d.levelMass^(-2:ℤ) * (2004:ℝ)^(-(1/2:ℝ)))^2 =
      (d.levelMass^4 * 2004)⁻¹ := by
  have hr : ((2004:ℝ)^(-(1/2:ℝ)))^2 = (2004:ℝ)⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2004)]
    norm_num
  rw [mul_pow,hr]
  norm_num only [zpow_neg,zpow_ofNat]
  field_simp

theorem normalization_weighted_identity (d : PositiveDistanceData) :
    d.normalization.toReal = (2004*(2:ℝ)^((d.t:ℝ)-d.a)) *
      (d.levelMass^(-2:ℤ) * (2004:ℝ)^(-(1/2:ℝ)))^2 := by
  rw [normalization,ENNReal.toReal_ofReal (by positivity),d.weighted_lower_constant_sq]
  field_simp

theorem weightedDistance_collision_lower (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (hcarry : d.ρ d.Q.carrierᶜ = 0)
    (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    (d.levelMass^(-2:ℤ) * (2004:ℝ)^(-(1/2:ℝ)))^2 * (d.distance.prod d.distance).real S ≤
      (d.weightedDistance.prod d.weightedDistance).real S := by
  let := d.weightedDistance_isFinite hQ hs
  have hc : 0 ≤ d.levelMass^(-2:ℤ) * (2004:ℝ)^(-(1/2:ℝ)) := by positivity
  have hp := Measure.prod_mono (d.weightedDistance_lower hQ hs hcarry)
    (d.weightedDistance_lower hQ hs hcarry)
  have h := ENNReal.toReal_mono (measure_ne_top (d.weightedDistance.prod d.weightedDistance) S)
    (Measure.le_iff.mp hp S hS)
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,Measure.smul_apply,
    smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc] at h
  simpa only [pow_two,measureReal_def] using h

theorem coincidence_le_weighted_collision (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (hcarry : d.ρ d.Q.carrierᶜ = 0) :
    d.coincidence.toReal ≤ 2004*(2:ℝ)^((d.t:ℝ)-d.a) *
      (d.weightedDistance.prod d.weightedDistance).real
        {z : ℝ × ℝ | |z.1-z.2| ≤ 100*d.width} := by
  have h := d.weightedDistance_collision_lower hQ hs hcarry
    {z : ℝ × ℝ | |z.1-z.2| ≤ 100*d.width} (by measurability)
  have he : d.coincidence.toReal = d.normalization.toReal *
      (d.distance.prod d.distance).real {z : ℝ × ℝ | |z.1-z.2| ≤ 100*d.width} := by
    rw [coincidence,ENNReal.toReal_mul,measureReal_def,d.distance_collision]
  rw [he,d.normalization_weighted_identity,mul_assoc]
  exact mul_le_mul_of_nonneg_left h (by positivity)

end PositiveDistanceData

end PlanarFalconer

end OAI
