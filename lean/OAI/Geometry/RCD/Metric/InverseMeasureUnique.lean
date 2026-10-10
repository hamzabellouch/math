import OAI.Geometry.RCD.Transport.ObservableSubplans

namespace OAI

/-! # A common almost-everywhere inverse determines submeasures by their image -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem measure_eq_of_common_ae_inverse (μ ν ρ : Measure A)
    {f : A → B} {g : B → A} (hf : Measurable f) (hg : Measurable g)
    (hinv : ∀ᵐ a ∂μ, g (f a)=a) (hν : ν ≪ μ) (hρ : ρ ≪ μ)
    (he : ν.map f=ρ.map f) : ν=ρ := by
  have hν' : (ν.map f).map g=ν := by
    rw [Measure.map_map hg hf]
    calc
      ν.map (g ∘ f)=ν.map id := Measure.map_congr (hinv.filter_mono hν.ae_le)
      _ = ν := Measure.map_id
  have hρ' : (ρ.map f).map g=ρ := by
    rw [Measure.map_map hg hf]
    calc
      ρ.map (g ∘ f)=ρ.map id := Measure.map_congr (hinv.filter_mono hρ.ae_le)
      _ = ρ := Measure.map_id
  rw [←hν',←hρ',he]

end RegularPointCoordinates

end

end OAI
