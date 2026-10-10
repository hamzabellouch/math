import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

/-! # Incidence mass lost when either original marginal is restricted -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem product_restriction_incidence_loss (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (E : Set (X × Y)) (hE : MeasurableSet E)
    (P : Set X) (Q : Set Y) :
    (μ.prod ν) E ≤ (μ.restrict P).prod (ν.restrict Q) E +
      μ Pᶜ*ν univ + μ univ*ν Qᶜ := by
  have hs : E ⊆ (E ∩ (P ×ˢ Q)) ∪ (Pᶜ ×ˢ univ) ∪ (univ ×ˢ Qᶜ) := by
    intro z hz
    by_cases hp : z.1 ∈ P
    · by_cases hq : z.2 ∈ Q
      · exact Or.inl (Or.inl ⟨hz,hp,hq⟩)
      · exact Or.inr ⟨mem_univ _,hq⟩
    · exact Or.inl (Or.inr ⟨hp,mem_univ _⟩)
  rw [Measure.prod_restrict,Measure.restrict_apply hE]
  calc
    _ ≤ (μ.prod ν) ((E ∩ (P ×ˢ Q)) ∪ (Pᶜ ×ˢ univ) ∪ (univ ×ˢ Qᶜ)) := measure_mono hs
    _ ≤ (μ.prod ν) ((E ∩ (P ×ˢ Q)) ∪ (Pᶜ ×ˢ univ)) + (μ.prod ν) (univ ×ˢ Qᶜ) :=
      measure_union_le _ _
    _ ≤ ((μ.prod ν) (E ∩ (P ×ˢ Q)) + (μ.prod ν) (Pᶜ ×ˢ univ)) +
        (μ.prod ν) (univ ×ˢ Qᶜ) := add_le_add_left (measure_union_le _ _) _
    _ = _ := by rw [Measure.prod_prod,Measure.prod_prod]

theorem product_incidence_relation_loss (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (E F : Set (X × Y)) :
    (μ.prod ν) E ≤ (μ.prod ν) (E ∩ F) + (μ.prod ν) Fᶜ := by
  apply (measure_mono (show E ⊆ (E ∩ F) ∪ Fᶜ from ?_)).trans (measure_union_le _ _)
  intro z hz
  by_cases hf : z ∈ F
  · exact Or.inl ⟨hz,hf⟩
  · exact Or.inr hf

end Falconer

end OAI
