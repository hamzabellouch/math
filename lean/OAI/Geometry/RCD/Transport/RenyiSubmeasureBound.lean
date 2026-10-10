import OAI.Geometry.RCD.Transport.RenyiInverseDensity

namespace OAI

/-! # Inverse-density lower bounds for a submeasure's Rényi integral

The ambient density can be used even when endpoint length components
overlap. Its negative power is smaller than the component density's power.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem inverse_density_lintegral_le_renyi (μ ν η : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure η] (hac : ν ≪ μ) (hη : η≤ν)
    {N : ℝ} (hN : 1<N) :
    (∫⁻ x, (ν.rnDeriv μ x)^(-(1/N)) ∂η)≤renyiIntegral μ η N := by
  have hsum : (ν-η)+η=ν := Measure.sub_add_cancel_of_le hη
  have hle : η.rnDeriv μ≤ᵐ[μ]ν.rnDeriv μ := by
    filter_upwards [Measure.rnDeriv_add (ν-η) η μ] with x hx
    rw [hsum] at hx
    rw [hx]
    exact le_add_left le_rfl
  have hηac : η ≪ μ := hη.absolutelyContinuous.trans hac
  rw [renyiIntegral_eq_inverse_density μ η hηac hN]
  apply lintegral_mono_ae
  filter_upwards [hle.filter_mono hηac.ae_le] with x hx
  rw [ENNReal.rpow_neg,ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hx (by positivity))

end RegularPointCoordinates

end

end OAI
