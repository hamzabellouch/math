import OAI.MeasureTheory.Falconer.Estimates.PositiveDistanceWeight
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

noncomputable def weightedPair (d : PositiveDistanceData) : Measure (Plane × Plane) :=
  d.cellPair.withDensity (fun z => ENNReal.ofReal (d.levelMass^(-2:ℤ) * d.spatialWeight z))

noncomputable def weightedDistance (d : PositiveDistanceData) : Measure ℝ :=
  Measure.map (fun z : Plane × Plane => dist z.1 z.2) d.weightedPair

theorem weightedPair_le (d : PositiveDistanceData) [SFinite d.ρ] (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) :
    d.weightedPair ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) • d.cellPair := by
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [d.ae_cellPair_mem] with z hz
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_of_le_one_right (by positivity) (d.spatialWeight_le_one hQ hs hz.1 hz.2)

theorem weightedPair_isFinite (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) : IsFiniteMeasure d.weightedPair := by
  constructor
  apply (Measure.le_iff.mp (d.weightedPair_le hQ hs) univ MeasurableSet.univ).trans_lt
  rw [Measure.smul_apply,smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem weightedDistance_isFinite (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) : IsFiniteMeasure d.weightedDistance := by
  let := d.weightedPair_isFinite hQ hs
  unfold weightedDistance
  infer_instance

theorem weightedPair_lower (d : PositiveDistanceData) [SFinite d.ρ] (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) (hcarry : d.ρ d.Q.carrierᶜ = 0) :
    ENNReal.ofReal (d.levelMass^(-2:ℤ) * (2004:ℝ)^(-(1/2:ℝ))) • d.pair ≤
      d.weightedPair := by
  rw [pair,← withDensity_const,← withDensity_indicator d.measurable_good]
  apply withDensity_mono
  filter_upwards [d.ae_spatialWeight_bounds hQ hs hcarry] with z hz
  by_cases hg : z ∈ d.good
  · rw [Set.indicator_of_mem hg]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hz.2 hg) (by positivity))
  · rw [Set.indicator_of_notMem hg]
    exact zero_le

theorem weightedDistance_lower (d : PositiveDistanceData) [SFinite d.ρ] (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) (hcarry : d.ρ d.Q.carrierᶜ = 0) :
    ENNReal.ofReal (d.levelMass^(-2:ℤ) * (2004:ℝ)^(-(1/2:ℝ))) • d.distance ≤
      d.weightedDistance := by
  have h := Measure.map_mono (d.weightedPair_lower hQ hs hcarry)
    (continuous_fst.dist continuous_snd).measurable
  rw [Measure.map_smul _ (continuous_fst.dist continuous_snd).measurable.aemeasurable] at h
  exact h

theorem lintegral_weightedDistance (d : PositiveDistanceData)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s, F s ∂d.weightedDistance) =
      ∫⁻ z, ENNReal.ofReal (d.levelMass^(-2:ℤ) * d.spatialWeight z) *
        F (dist z.1 z.2) ∂d.cellPair := by
  rw [weightedDistance,lintegral_map hF (by fun_prop),weightedPair,
    lintegral_withDensity_eq_lintegral_mul]
  · rfl
  · exact (measurable_const.mul d.measurable_spatialWeight).ennreal_ofReal
  · exact hF.comp (continuous_fst.dist continuous_snd).measurable

theorem integral_weightedDistance (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (F : ℝ → ℂ) (hF : AEStronglyMeasurable F d.weightedDistance) :
    (∫ s, F s ∂d.weightedDistance) =
      ∫ z, (d.levelMass^(-2:ℤ) * d.spatialWeight z) • F (dist z.1 z.2) ∂d.cellPair := by
  rw [weightedDistance,integral_map (by fun_prop) hF,weightedPair]
  have hw : Measurable (fun z : Plane × Plane =>
      ENNReal.ofReal (d.levelMass^(-2:ℤ) * d.spatialWeight z)) :=
    ((measurable_const : Measurable (fun _ : Plane × Plane => d.levelMass^(-2:ℤ))).mul
      d.measurable_spatialWeight).ennreal_ofReal
  calc
    _ = ∫ z, (ENNReal.ofReal (d.levelMass^(-2:ℤ) * d.spatialWeight z)).toReal •
        F (dist z.1 z.2) ∂d.cellPair :=
      integral_withDensity_eq_integral_toReal_smul hw
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity) (d.spatialWeight_nonneg hQ z))]

end PositiveDistanceData

end PlanarFalconer

end OAI
