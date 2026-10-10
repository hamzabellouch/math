import Mathlib

namespace OAI

universe uAlpha uBeta uIndex

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- Equal cell-label laws let one compare costs using only their oscillation inside
matching cells. The target-cell condition is needed only on a full-measure set. -/
theorem lintegral_le_of_same_cells
    {α : Type uAlpha} {β : Type uBeta} {ι : Type uIndex} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    (p : α → ι) (q : β → ι) (hp : Measurable p) (hq : Measurable q)
    (hlaw : Measure.map p μ = Measure.map q ν)
    (f : α → ℝ≥0∞) (g : β → ℝ≥0∞) (ε : ℝ≥0∞)
    (t : Set β) (ht : ∀ᵐ y ∂ν, y ∈ t)
    (hosc : ∀ᵐ x ∂μ, ∀ y ∈ t, p x = q y → f x ≤ g y + ε) :
    (∫⁻ x, f x ∂μ) ≤ (∫⁻ y, g y ∂ν) + ε := by
  let c : ι → ℝ≥0∞ := fun i => ⨅ y ∈ t, ⨅ (_ : q y = i), g y
  have hc : Measurable c := measurable_of_countable c
  have hupper : f ≤ᵐ[μ] fun x => c (p x) + ε := by
    filter_upwards [hosc] with x hx
    simp only [c, ENNReal.iInf_add]
    exact le_iInf fun y => le_iInf fun hy => le_iInf fun hi => hx y hy hi.symm
  have hlower : (fun y => c (q y)) ≤ᵐ[ν] g := by
    filter_upwards [ht] with y hy
    exact iInf_le_of_le y (iInf_le_of_le hy (iInf_le_of_le rfl le_rfl))
  have htransport : (∫⁻ x, c (p x) ∂μ) = ∫⁻ y, c (q y) ∂ν := by
    rw [← lintegral_map hc hp, hlaw, lintegral_map hc hq]
  calc
    (∫⁻ x, f x ∂μ) ≤ ∫⁻ x, c (p x) + ε ∂μ := lintegral_mono_ae hupper
    _ = (∫⁻ x, c (p x) ∂μ) + ε := by
      rw [lintegral_add_right _ measurable_const]
      simp
    _ = (∫⁻ y, c (q y) ∂ν) + ε := by rw [htransport]
    _ ≤ (∫⁻ y, g y ∂ν) + ε := add_le_add (lintegral_mono_ae hlower) le_rfl

end Problem356

end OAI
