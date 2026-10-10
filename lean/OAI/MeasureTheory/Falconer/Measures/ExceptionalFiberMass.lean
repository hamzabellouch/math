import OAI.MeasureTheory.Falconer.Estimates.SphericalEnergy

namespace OAI

/-! # Integrating a uniform fiber bound outside a measurable exceptional set -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem product_mass_of_exceptional_fibers (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (G : Set (X × Y)) (hG : MeasurableSet G) (E : Set X) (hE : MeasurableSet E)
    {B : ℝ≥0∞} (hfiber : ∀ᵐ x ∂μ, x ∉ E → ν {y | (x,y) ∈ G} ≤ B) :
    (μ.prod ν) G ≤ μ E+B := by
  rw [Measure.prod_apply hG]
  calc
    _ ≤ ∫⁻ x, E.indicator (fun _ => (1:ℝ≥0∞)) x+B ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hfiber] with x hx
      by_cases hxe : x ∈ E
      · rw [indicator_of_mem hxe]
        exact (prob_le_one).trans (le_add_right le_rfl)
      · rw [indicator_of_notMem hxe,zero_add]
        exact hx hxe
    _ = _ := by
      rw [lintegral_add_left (measurable_const.indicator hE),
        lintegral_indicator_const hE,lintegral_const,measure_univ,one_mul,mul_one]

end Falconer

end OAI
