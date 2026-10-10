import OAI.Geometry.RCD.Sobolev.LocalEnergyMap

namespace OAI

/-! # Compact weights against the actual image energy measure -/

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem localEnergyMeasure_map_integral (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (w : SobolevSpace μ hQ) (A : Set X) {c : ℝ} (hc : 0≤c)
    {v : X → Y} (hv : Measurable v) (φ : Y →ᵇ ℝ) :
    (∫ z, φ z ∂((localEnergyMeasure μ hQ w A c).map v : Measure Y))=
      c*∫ x in A, φ (v x)*localGamma μ hQ w w x ∂μ := by
  change (∫ z, φ z ∂(localEnergyMeasure μ hQ w A c : Measure X).map v)=_
  rw [integral_map hv.aemeasurable φ.continuous.aestronglyMeasurable]
  change (∫ x, φ (v x) ∂(μ.restrict A).withDensity
    (fun x => ENNReal.ofReal (c*localGamma μ hQ w w x)))=_
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (((localGamma_memL1 μ hQ w w).restrict.const_mul c).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ x in A, c*(φ (v x)*localGamma μ hQ w w x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (localGamma_self μ hQ w)] with x hx
      rw [ENNReal.toReal_ofReal (mul_nonneg hc (hx ▸ sq_nonneg _)),smul_eq_mul]
      ring
    _ = _ := integral_const_mul _ _

end RegularPointCoordinates

end

end OAI
