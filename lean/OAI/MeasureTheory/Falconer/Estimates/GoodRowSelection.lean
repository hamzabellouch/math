import OAI.MeasureTheory.Falconer.Incidence.BadRowIncidence
import OAI.MeasureTheory.Falconer.Slicing.SliceSelectionMean

namespace OAI

/-! # A retained incidence slice with simultaneous pair and triple cost bounds -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]

theorem good_row_selection (ξ : Measure A) (ν : Measure Z) [SFinite ξ] [SFinite ν]
    (hξ : ξ univ ≤ 1) (F : A × Z → ℝ≥0∞) (hF : Measurable F)
    (B₁ B₂ : A → ℝ≥0∞) (hB₁ : Measurable B₁) (hB₂ : Measurable B₂)
    (S : Set Z) (hS : MeasurableSet S) (M t₁ t₂ a : ℝ≥0∞)
    (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) (ht₁top : t₁ ≠ ∞) (ht₂top : t₂ ≠ ∞)
    (hbound : ∀ p, F p ≤ M) (hsupport : ∀ p, p.2 ∉ S → F p = 0)
    (hmean : a*ν S+(M*ν S)*((∫⁻ x, B₁ x ∂ξ)/t₁)+
      (M*ν S)*((∫⁻ x, B₂ x ∂ξ)/t₂) < ∫⁻ p, F p ∂ξ.prod ν) :
    ∃ x z, z ∈ S ∧ B₁ x < t₁ ∧ B₂ x < t₂ ∧ a < F (x,z) := by
  let T₁ : Set (A × Z) := {p | t₁ ≤ B₁ p.1}
  let T₂ : Set (A × Z) := {p | t₂ ≤ B₂ p.1}
  let G : Set (A × Z) := T₁ᶜ ∩ T₂ᶜ
  have hm₁ : MeasurableSet T₁ := measurableSet_le measurable_const (hB₁.comp measurable_fst)
  have hm₂ : MeasurableSet T₂ := measurableSet_le measurable_const (hB₂.comp measurable_fst)
  have hG : MeasurableSet G := hm₁.compl.inter hm₂.compl
  let f := G.indicator F
  have hf : Measurable f := hF.indicator hG
  have hlo : ∫⁻ p, F p ∂ξ.prod ν ≤
      (∫⁻ p, f p ∂ξ.prod ν)+(∫⁻ p in T₁, F p ∂ξ.prod ν)+
        (∫⁻ p in T₂, F p ∂ξ.prod ν) := by
    rw [← lintegral_indicator hm₁,← lintegral_indicator hm₂,
      ← lintegral_add_left hf,← lintegral_add_left (f := fun p => f p+T₁.indicator F p) (hf.add (hF.indicator hm₁))]
    apply lintegral_mono
    intro p
    by_cases h₁ : p ∈ T₁
    · simp only [indicator_of_mem h₁]
      exact le_add_of_le_left (le_add_left le_rfl)
    · by_cases h₂ : p ∈ T₂
      · simp only [indicator_of_mem h₂]
        exact le_add_left le_rfl
      · have hp : p ∈ G := ⟨h₁,h₂⟩
        simp only [f,indicator_of_mem hp,indicator_of_notMem h₁,indicator_of_notMem h₂,add_zero]
        exact le_rfl
  have hbad₁ := bad_row_incidence ξ ν F B₁ hB₁ S hS M t₁ ht₁ ht₁top hbound hsupport
  have hbad₂ := bad_row_incidence ξ ν F B₂ hB₂ S hS M t₂ ht₂ ht₂top hbound hsupport
  have hi : a*ν S < ∫⁻ p, f p ∂ξ.prod ν := by
    have hh := hmean.trans_le (hlo.trans (add_le_add (add_le_add le_rfl hbad₁) hbad₂))
    exact lt_of_add_lt_add_right (lt_of_add_lt_add_right hh)
  let U : Set (A × Z) := G ∩ (univ ×ˢ S)
  have hU : MeasurableSet U := hG.inter (MeasurableSet.univ.prod hS)
  have hmass : (ξ.prod ν) U ≤ ν S := by
    apply (measure_mono (inter_subset_right)).trans
    rw [Measure.prod_prod]
    simpa only [one_mul] using mul_le_mul' hξ le_rfl
  have hsu : ∀ p, p ∉ U → f p = 0 := by
    intro p hp
    by_cases hg : p ∈ G
    · have hz : p.2 ∉ S := fun hz => hp ⟨hg,mem_univ _,hz⟩
      simp only [f,indicator_of_mem hg,hsupport p hz]
    · simp only [f,indicator_of_notMem hg]
  obtain ⟨⟨x,z⟩,hp,hlarge⟩ := exists_large_slice_of_mean (ξ.prod ν) U hU f
    (Filter.Eventually.of_forall hsu) ((mul_le_mul' le_rfl hmass).trans_lt hi)
  have hg : (x,z) ∈ G := hp.1
  refine ⟨x,z,hp.2.2,lt_of_not_ge hg.1,lt_of_not_ge hg.2,?_⟩
  simpa only [f,indicator_of_mem hg] using hlarge

end Falconer

end OAI
