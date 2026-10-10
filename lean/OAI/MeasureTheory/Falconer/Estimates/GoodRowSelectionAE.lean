import OAI.MeasureTheory.Falconer.Estimates.GoodRowSelection

namespace OAI

/-! # Good-row selection with the actual almost-everywhere slice support -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]

theorem good_row_selection_ae (ξ : Measure A) (ν : Measure Z) [SFinite ξ] [SFinite ν]
    (hξ : ξ univ ≤ 1) (F : A × Z → ℝ≥0∞) (hF : Measurable F)
    (B₁ B₂ : A → ℝ≥0∞) (hB₁ : Measurable B₁) (hB₂ : Measurable B₂)
    (S : Set Z) (hS : MeasurableSet S) (M t₁ t₂ a : ℝ≥0∞)
    (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) (ht₁top : t₁ ≠ ∞) (ht₂top : t₂ ≠ ∞)
    (hbound : ∀ p, F p ≤ M)
    (hsupport : ∀ᵐ p ∂ξ.prod ν, p.2 ∉ S → F p = 0)
    (hmean : a*ν S+(M*ν S)*((∫⁻ x, B₁ x ∂ξ)/t₁)+
      (M*ν S)*((∫⁻ x, B₂ x ∂ξ)/t₂) < ∫⁻ p, F p ∂ξ.prod ν) :
    ∃ x z, z ∈ S ∧ B₁ x < t₁ ∧ B₂ x < t₂ ∧ a < F (x,z) := by
  let F' := (univ ×ˢ S).indicator F
  have hm : Measurable F' := hF.indicator (MeasurableSet.univ.prod hS)
  have hi : (∫⁻ p, F' p ∂ξ.prod ν) = ∫⁻ p, F p ∂ξ.prod ν := by
    apply lintegral_congr_ae
    filter_upwards [hsupport] with p hp
    by_cases hs : p.2 ∈ S
    · exact indicator_of_mem (show p ∈ univ ×ˢ S from ⟨mem_univ _,hs⟩) F
    · rw [show F' p = 0 from indicator_of_notMem (fun h => hs h.2) F,hp hs]
  have hbound' : ∀ p, F' p ≤ M := by
    intro p
    by_cases hp : p.2 ∈ S
    · simpa only [F',indicator_of_mem (show p ∈ univ ×ˢ S from ⟨mem_univ _,hp⟩)] using hbound p
    · rw [show F' p = 0 from indicator_of_notMem (fun h => hp h.2) F]
      exact bot_le
  have hsupport' : ∀ p : A × Z, p.2 ∉ S → F' p = 0 := by
    intro p hp
    exact indicator_of_notMem (fun h => hp h.2) F
  obtain ⟨x,z,hz,h₁,h₂,hlarge⟩ := good_row_selection ξ ν hξ F' hm B₁ B₂ hB₁ hB₂
    S hS M t₁ t₂ a ht₁ ht₂ ht₁top ht₂top hbound' hsupport' (by rw [hi]; exact hmean)
  refine ⟨x,z,hz,h₁,h₂,?_⟩
  simpa only [F',indicator_of_mem (show (x,z) ∈ univ ×ˢ S from ⟨mem_univ _,hz⟩)] using hlarge

end Falconer

end OAI
