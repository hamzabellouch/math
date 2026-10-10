import OAI.Geometry.RCD.Transport.RenyiSubplanMaximality

namespace OAI

/-! # Scaling the Rényi functional for normalized transport components -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem renyiPower_smul (μ ν : Measure X) [SigmaFinite μ] [IsFiniteMeasure ν]
    {c : ℝ≥0∞} (hc : c≠∞) (q : ℝ) :
    (∫ x, ((c • ν).rnDeriv μ x).toReal^q ∂μ)=
      c.toReal^q*(∫ x, (ν.rnDeriv μ x).toReal^q ∂μ) := by
  calc
    _ = ∫ x, c.toReal^q*(ν.rnDeriv μ x).toReal^q ∂μ := by
      apply integral_congr_ae
      filter_upwards [Measure.rnDeriv_smul_left_of_ne_top ν μ hc] with x hx
      rw [hx]
      change (c*ν.rnDeriv μ x).toReal^q=_
      rw [ENNReal.toReal_mul,Real.mul_rpow ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
    _ = _ := integral_const_mul _ _

end RegularPointCoordinates

end

end OAI
