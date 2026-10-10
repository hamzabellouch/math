import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3

noncomputable section

open MeasureTheory

namespace Problem336AdditiveD139.IIDAction

variable {Γ : Type u_1} {α : Type u_2} {β : Type u_3} [Group Γ]

@[simp]theorem leftTranslate_one (a : Γ → α) : leftTranslate (1 : Γ) a = a := by
  funext h
  simp [leftTranslate]

theorem leftTranslate_mul (g h : Γ) (a : Γ → α) :
    leftTranslate (g * h) a = leftTranslate g (leftTranslate h a) := by
  funext k
  simp [leftTranslate, mul_assoc]

@[simp]theorem leftTranslate_inv (g : Γ) (a : Γ → α) :
    leftTranslate g⁻¹ (leftTranslate g a) = a := by
  rw [← leftTranslate_mul]
  simp

@[simp]theorem leftTranslate_const (g : Γ) (a : α) :
    leftTranslate g (fun _ : Γ => a) = fun _ => a := rfl

theorem measurable_leftTranslate [MeasurableSpace α] (g : Γ) :
    Measurable (leftTranslate g : (Γ → α) → Γ → α) := by
  exact Measurable.of_eval fun h => measurable_pi_apply (g⁻¹ * h)

theorem coordinateMap_equivariant (f : α → β) (g : Γ) (u : Γ → α) :
    (fun i => f (leftTranslate g u i)) = leftTranslate g (fun i => f (u i)) := rfl

omit [Group Γ] in
theorem measurable_coordinateMap [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) : Measurable (fun u : Γ → α => fun i => f (u i)) := by
  exact Measurable.of_eval fun i => hf.comp (measurable_pi_apply i)

omit [Group Γ] in
theorem isProbabilityMeasure_iidUnitLabels [MeasurableSpace Γ] :
    IsProbabilityMeasure (iidUnitLabels Γ) := by
  unfold iidUnitLabels
  infer_instance

theorem map_leftTranslate_iidUnitLabels [MeasurableSpace Γ] (g : Γ) :
    Measure.map (leftTranslate g) (iidUnitLabels Γ) = iidUnitLabels Γ := by
  unfold iidUnitLabels leftTranslate
  exact Measure.map_infinitePi_infinitePi_of_inj (mul_right_injective g⁻¹)

theorem measurePreserving_leftTranslate_iidUnitLabels [MeasurableSpace Γ] (g : Γ) :
    MeasurePreserving (leftTranslate g) (iidUnitLabels Γ) (iidUnitLabels Γ) :=
  ⟨measurable_leftTranslate g, map_leftTranslate_iidUnitLabels g⟩

omit [Group Γ] in
theorem map_coordinatewise [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure α) [IsProbabilityMeasure ρ] (f : α → β) (hf : Measurable f) :
    Measure.map (fun u : Γ → α => fun i => f (u i))
      (Measure.infinitePi (fun _ : Γ => ρ)) =
        Measure.infinitePi (fun _ : Γ => Measure.map f ρ) := by
  exact Measure.infinitePi_map_pi _ (fun _ => hf)

theorem factor_of_coordinatewise_decoder [MeasurableSpace Γ] [MeasurableSpace α]
    (ρ : Measure α) (f : UnitLabel → α) (hf : Measurable f)
    (hfρ : Measure.map f volume = ρ)
    (μ : ProbabilityMeasure (Γ → Bool))
    (Ψ : (Γ → α) → Γ → Bool) (hΨ : Measurable Ψ)
    (hΨeq : ∀ g u, Ψ (leftTranslate g u) = leftTranslate g (Ψ u))
    (hΨlaw : Measure.map Ψ (Measure.infinitePi (fun _ : Γ => ρ)) =
      (μ : Measure (Γ → Bool))) : HasEquivariantIIDFactor μ := by
  refine ⟨fun u => Ψ (fun i => f (u i)), hΨ.comp (measurable_coordinateMap f hf), ?_, ?_⟩
  · intro g u
    exact hΨeq g (fun i => f (u i))
  · rw [show (fun u : Γ → UnitLabel => Ψ (fun i => f (u i))) =
        Ψ ∘ (fun u : Γ → UnitLabel => fun i => f (u i)) from rfl]
    rw [← Measure.map_map hΨ (measurable_coordinateMap f hf)]
    rw [iidUnitLabels, map_coordinatewise volume f hf, hfρ, hΨlaw]

theorem factor_of_standardBorel_decoder [MeasurableSpace Γ] [MeasurableSpace α]
    [Nonempty α] [StandardBorelSpace α] (ρ : Measure α) [IsProbabilityMeasure ρ]
    (μ : ProbabilityMeasure (Γ → Bool))
    (Ψ : (Γ → α) → Γ → Bool) (hΨ : Measurable Ψ)
    (hΨeq : ∀ g u, Ψ (leftTranslate g u) = leftTranslate g (Ψ u))
    (hΨlaw : Measure.map Ψ (Measure.infinitePi (fun _ : Γ => ρ)) =
      (μ : Measure (Γ → Bool))) : HasEquivariantIIDFactor μ := by
  obtain ⟨f, hf, hfρ⟩ := ρ.exists_measurable_map_eq
  exact factor_of_coordinatewise_decoder ρ f hf hfρ μ Ψ hΨ hΨeq hΨlaw

end Problem336AdditiveD139.IIDAction

end

end OAI
