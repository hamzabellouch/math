import OAI.MeasureTheory.Falconer.Estimates.WeightedDistancePushforward
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem weightedDistance_fourier (d : PositiveDistanceData) (hQ : 0 < d.Q.side) (r : ℝ) :
    charFun d.weightedDistance r =
      (d.levelMass^(-2:ℤ):ℝ) • ∫ z, (d.spatialWeight z : ℂ) *
        Complex.exp ((r*dist z.1 z.2:ℝ)*Complex.I) ∂d.cellPair := by
  rw [charFun_apply_real,d.integral_weightedDistance hQ _ (by fun_prop)]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Complex.real_smul,Complex.ofReal_mul]
  ring

theorem weightedDistance_fourier_norm (d : PositiveDistanceData) (r : ℝ) :
    ‖charFun d.weightedDistance r‖ ≤ d.weightedDistance.real univ := norm_charFun_le r

theorem weightedDistance_fourier_interval (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (a b : ℝ) :
    IntervalIntegrable (charFun d.weightedDistance) volume a b := by
  let := d.weightedDistance_isFinite hQ hs
  exact intervalIntegrable_charFun

end PositiveDistanceData

end PlanarFalconer

end OAI
