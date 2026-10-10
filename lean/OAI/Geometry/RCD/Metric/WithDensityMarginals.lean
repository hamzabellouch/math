import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # Marginals of a product measure with a measurable density -/

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]

theorem product_density_fst (h : A × B → ℝ≥0∞) (hh : Measurable h) :
    ((μ.prod ν).withDensity h).map Prod.fst =
      μ.withDensity (fun a => ∫⁻ b, h (a,b) ∂ν) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs,withDensity_apply _ (measurable_fst hs),
    show Prod.fst ⁻¹' s = s ×ˢ (univ : Set B) by ext x; simp,
    setLIntegral_prod _ hh.aemeasurable,withDensity_apply _ hs]
  simp only [Measure.restrict_univ]

theorem product_density_snd (h : A × B → ℝ≥0∞) (hh : Measurable h) :
    ((μ.prod ν).withDensity h).map Prod.snd =
      ν.withDensity (fun b => ∫⁻ a, h (a,b) ∂μ) := by
  ext s hs
  rw [Measure.map_apply measurable_snd hs,withDensity_apply _ (measurable_snd hs),
    show Prod.snd ⁻¹' s = (univ : Set A) ×ˢ s by ext x; simp,
    setLIntegral_prod_symm _ hh.aemeasurable,withDensity_apply _ hs]
  simp only [Measure.restrict_univ]

end RegularPointCoordinates

end

end OAI
