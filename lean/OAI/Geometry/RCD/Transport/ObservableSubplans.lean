import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MutuallySingular

namespace OAI

/-! # An observable with a measurable inverse retains measurable subplans -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem restrict_map_of_ae_left_inverse (μ : Measure A) {f : A → B} {g : B → A}
    (hf : Measurable f) (hg : Measurable g) (hinv : ∀ᵐ a ∂μ, g (f a)=a)
    {S : Set A} (hS : MeasurableSet S) :
    (μ.restrict S).map f=(μ.map f).restrict (g ⁻¹' S) := by
  rw [Measure.restrict_map hf (hS.preimage hg)]
  congr 1
  apply Measure.restrict_congr_set
  filter_upwards [hinv] with a ha
  change (a ∈ S)=(g (f a) ∈ S)
  rw [ha]

theorem mapped_restrictions_mutuallySingular (μ : Measure A) {f : A → B} {g : B → A}
    (hf : Measurable f) (hg : Measurable g) (hinv : ∀ᵐ a ∂μ, g (f a)=a)
    {S : Set A} (hS : MeasurableSet S) :
    (μ.restrict S).map f ⟂ₘ (μ.restrict Sᶜ).map f := by
  rw [restrict_map_of_ae_left_inverse μ hf hg hinv hS,
    restrict_map_of_ae_left_inverse μ hf hg hinv hS.compl,preimage_compl]
  refine ⟨(g ⁻¹' S)ᶜ,(hS.preimage hg).compl,?_,?_⟩
  · rw [Measure.restrict_apply (hS.preimage hg).compl,compl_inter_self,measure_empty]
  · rw [compl_compl,Measure.restrict_apply (hS.preimage hg),inter_compl_self,measure_empty]

theorem mutuallySingular_map_of_ae_left_inverse (μ ν ρ : Measure A)
    {f : A → B} {g : B → A} (hf : Measurable f) (hg : Measurable g)
    (hinv : ∀ᵐ a ∂μ, g (f a)=a) (hν : ν ≪ μ) (hρ : ρ ≪ μ)
    (hs : ν ⟂ₘ ρ) : ν.map f ⟂ₘ ρ.map f := by
  obtain ⟨S,hS,hνS,hρS⟩ := hs
  refine ⟨g ⁻¹' S,hS.preimage hg,?_,?_⟩
  · rw [Measure.map_apply hf (hS.preimage hg)]
    calc
      ν (f ⁻¹' (g ⁻¹' S)) = ν S := by
        apply measure_congr
        filter_upwards [hinv.filter_mono hν.ae_le] with a ha
        change (g (f a) ∈ S)=(a ∈ S)
        rw [ha]
      _ = 0 := hνS
  · rw [←preimage_compl,Measure.map_apply hf (hS.compl.preimage hg)]
    calc
      ρ (f ⁻¹' (g ⁻¹' Sᶜ)) = ρ Sᶜ := by
        apply measure_congr
        filter_upwards [hinv.filter_mono hρ.ae_le] with a ha
        change (g (f a) ∈ Sᶜ)=(a ∈ Sᶜ)
        rw [ha]
      _ = 0 := hρS

end RegularPointCoordinates

end

end OAI
