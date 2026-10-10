import OAI.Probability.StrongRayleigh.Model
import OAI.Probability.StrongRayleigh.InclusionUniqueness

namespace OAI

universe u_1 u_2 u_3

noncomputable section

open MeasureTheory

namespace Problem336AdditiveD139

theorem IsDeterminantalLaw.eq {I : Type u_1}
    {μ ν : ProbabilityMeasure (I → Bool)} {K : I → I → ℂ}
    (hμ : IsDeterminantalLaw μ K) (hν : IsDeterminantalLaw ν K) : μ = ν := by
  apply probabilityMeasure_eq_of_inclusion_probabilities_toReal μ ν
  intro A
  simpa using congrArg Complex.re ((hμ A).trans (hν A).symm)

theorem IsFiniteDeterminantalLaw.eq {F : Type u_2} [Fintype F]
    {μ ν : ProbabilityMeasure (F → Bool)} {K : F → F → ℂ}
    (hμ : IsFiniteDeterminantalLaw μ K) (hν : IsFiniteDeterminantalLaw ν K) : μ = ν :=
  IsDeterminantalLaw.eq hμ hν

theorem existsUnique_determinantalLaw_of_exists {I : Type u_3} (K : I → I → ℂ)
    (h : ∃ μ : ProbabilityMeasure (I → Bool), IsDeterminantalLaw μ K) :
    ∃! μ : ProbabilityMeasure (I → Bool), IsDeterminantalLaw μ K := by
  obtain ⟨μ, hμ⟩ := h
  exact ⟨μ, hμ, fun ν hν => hν.eq hμ⟩

end Problem336AdditiveD139

end

end OAI
