import OAI.Probability.StrongRayleigh.Translation
import OAI.Probability.StrongRayleigh.DeterminantalUniqueness

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section

open MeasureTheory

namespace Problem336AdditiveD139

theorem IsDeterminantalLaw.invariantBinaryLaw
    {Γ : Type u_1} [Group Γ] {K : Γ → Γ → ℂ}
    {μ : ProbabilityMeasure (Γ → Bool)}
    (hμ : IsDeterminantalLaw μ K) (hK : TranslationInvariantKernel K) :
    InvariantBinaryLaw μ := by
  intro g
  have heq : translatedLaw μ g = μ :=
    (translatedLaw_isDeterminantal hμ hK g).eq hμ
  exact congrArg ProbabilityMeasure.toMeasure heq

theorem translationInvariantKernel_factor_of_exists
    {Γ : Type u_2} [Group Γ] [MeasurableSpace Γ] (K : Γ → Γ → ℂ)
    (hK : TranslationInvariantKernel K)
    (hexists : ∃ μ : ProbabilityMeasure (Γ → Bool), IsDeterminantalLaw μ K)
    (hfactor : ∀ μ : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw μ K → InvariantBinaryLaw μ → HasEquivariantIIDFactor μ) :
    ∃ μ : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw μ K ∧ InvariantBinaryLaw μ ∧ HasEquivariantIIDFactor μ := by
  obtain ⟨μ, hμ⟩ := hexists
  have hinv := hμ.invariantBinaryLaw hK
  exact ⟨μ, hμ, hinv, hfactor μ hμ hinv⟩

theorem invariantBinaryLaw_of_unique_determinantal
    {Γ : Type u_3} [Group Γ] {K : Γ → Γ → ℂ}
    (μ : ProbabilityMeasure (Γ → Bool))
    (hunique : ∀ ν : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw ν K → ν = μ)
    (htranslate : ∀ g : Γ, ∃ ν : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw ν K ∧
        Measure.map (leftTranslate g) (μ : Measure (Γ → Bool)) =
          (ν : Measure (Γ → Bool))) :
    InvariantBinaryLaw μ := by
  intro g
  obtain ⟨ν, hν, hmap⟩ := htranslate g
  simpa only [hunique ν hν] using hmap

theorem determinantal_factor_of_existsUnique_of_translate
    {Γ : Type u_4} [Group Γ] [MeasurableSpace Γ] (K : Γ → Γ → ℂ)
    (hexists : ∃! μ : ProbabilityMeasure (Γ → Bool), IsDeterminantalLaw μ K)
    (htranslate : ∀ μ : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw μ K → ∀ g : Γ,
      ∃ ν : ProbabilityMeasure (Γ → Bool), IsDeterminantalLaw ν K ∧
        Measure.map (leftTranslate g) (μ : Measure (Γ → Bool)) =
          (ν : Measure (Γ → Bool)))
    (hfactor : ∀ μ : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw μ K → InvariantBinaryLaw μ → HasEquivariantIIDFactor μ) :
    ∃ μ : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw μ K ∧ InvariantBinaryLaw μ ∧ HasEquivariantIIDFactor μ := by
  obtain ⟨μ, hμ, hunique⟩ := hexists
  have hinv : InvariantBinaryLaw μ :=
    invariantBinaryLaw_of_unique_determinantal μ hunique (htranslate μ hμ)
  exact ⟨μ, hμ, hinv, hfactor μ hμ hinv⟩

theorem translationInvariantKernel_factor_of_existsUnique
    {Γ : Type u_5} [Group Γ] [MeasurableSpace Γ] (K : Γ → Γ → ℂ)
    (hK : TranslationInvariantKernel K)
    (hexists : ∃! μ : ProbabilityMeasure (Γ → Bool), IsDeterminantalLaw μ K)
    (hfactor : ∀ μ : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw μ K → InvariantBinaryLaw μ → HasEquivariantIIDFactor μ) :
    ∃ μ : ProbabilityMeasure (Γ → Bool),
      IsDeterminantalLaw μ K ∧ InvariantBinaryLaw μ ∧ HasEquivariantIIDFactor μ := by
  apply determinantal_factor_of_existsUnique_of_translate K hexists ?_ hfactor
  intro μ hμ g
  exact ⟨translatedLaw μ g, translatedLaw_isDeterminantal hμ hK g, rfl⟩

end Problem336AdditiveD139

end

end OAI
