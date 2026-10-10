import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Problem336AdditiveD139

lemma coordinatewise_leftTranslate {Γ : Type u_1} {α : Type u_2} {β : Type u_3} [Group Γ]
    (f : α → β) (g : Γ) (u : Γ → α) :
    (fun i => f (leftTranslate g u i)) =
      leftTranslate g (fun i => f (u i)) := rfl

theorem exists_equivariant_iid_source {Γ : Type u_4} {α : Type u_5} [Group Γ] [MeasurableSpace Γ]
    [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (ν : Measure α) [IsProbabilityMeasure ν] :
    ∃ F : (Γ → UnitLabel) → (Γ → α),
      Measurable F ∧
      (∀ (g : Γ) (u : Γ → UnitLabel),
        F (leftTranslate g u) = leftTranslate g (F u)) ∧
      Measure.map F (iidUnitLabels Γ) = Measure.infinitePi (fun _ : Γ => ν) := by
  obtain ⟨f, hf, hfν⟩ := ν.exists_measurable_map_eq
  refine ⟨fun u i => f (u i), ?_, ?_, ?_⟩
  · exact Measurable.of_eval (fun i => hf.comp (measurable_pi_apply i))
  · intro g u
    rfl
  · unfold iidUnitLabels
    rw [Measure.infinitePi_map_pi _ (fun _ => hf)]
    simp only [hfν]

theorem hasEquivariantIIDFactor_of_standardBorel_sampler
    {Γ : Type u_6} {α : Type u_7} [Group Γ] [MeasurableSpace Γ]
    [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (μ : ProbabilityMeasure (Γ → Bool))
    (Ψ : (Γ → α) → (Γ → Bool)) (hΨ : Measurable Ψ)
    (heq : ∀ (g : Γ) (w : Γ → α),
      Ψ (leftTranslate g w) = leftTranslate g (Ψ w))
    (hlaw : Measure.map Ψ (Measure.infinitePi (fun _ : Γ => ν)) =
      (μ : Measure (Γ → Bool))) :
    HasEquivariantIIDFactor μ := by
  obtain ⟨F, hF, hFeq, hFlaw⟩ := exists_equivariant_iid_source (Γ := Γ) ν
  refine ⟨Ψ ∘ F, hΨ.comp hF, ?_, ?_⟩
  · intro g u
    simp only [Function.comp_apply, hFeq, heq]
  · rw [← Measure.map_map hΨ hF, hFlaw, hlaw]

end Problem336AdditiveD139

end

end OAI
