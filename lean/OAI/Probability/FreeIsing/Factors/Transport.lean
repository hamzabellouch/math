import Mathlib

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.FactorTransport

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem map_invariant_of_ae_equivariant
    {μ : Measure α} {a : α → α} {b : β → β} {f : α → β}
    (ha : MeasurePreserving a μ μ) (hb : Measurable b) (hf : Measurable f)
    (heq : ∀ᵐ x ∂μ, f (a x) = b (f x)) :
    Measure.map b (Measure.map f μ) = Measure.map f μ := by
  calc
    Measure.map b (Measure.map f μ) = Measure.map (b ∘ f) μ :=
      Measure.map_map hb hf
    _ = Measure.map (f ∘ a) μ := Measure.map_congr (Filter.EventuallyEq.symm heq)
    _ = Measure.map f (Measure.map a μ) := (Measure.map_map hf ha.measurable).symm
    _ = Measure.map f μ := by rw [ha.map_eq]

omit [MeasurableSpace β] in

theorem ae_equivariant_congr
    {μ : Measure α} {a : α → α} {b : β → β} {f f' : α → β}
    (ha : Measure.QuasiMeasurePreserving a μ μ) (hff' : f =ᵐ[μ] f')
    (heq : ∀ᵐ x ∂μ, f (a x) = b (f x)) :
    ∀ᵐ x ∂μ, f' (a x) = b (f' x) := by
  filter_upwards [ha.ae hff', hff', heq] with x hx h'x heqx
  calc
    f' (a x) = f (a x) := hx.symm
    _ = b (f x) := heqx
    _ = b (f' x) := congrArg b h'x

omit [MeasurableSpace β] in

theorem ae_equivariant_countable
    {G : Type*} [Countable G] {μ : Measure α}
    (a : G → α → α) (b : G → β → β) (f : α → β)
    (heq : ∀ g, ∀ᵐ x ∂μ, f (a g x) = b g (f x)) :
    ∀ᵐ x ∂μ, ∀ g, f (a g x) = b g (f x) := by
  exact ae_all_iff.mpr heq

end Problem367.FactorTransport

end

end OAI
