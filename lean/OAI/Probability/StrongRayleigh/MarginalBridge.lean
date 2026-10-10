import OAI.Probability.StrongRayleigh.FiniteMarginal

namespace OAI

universe u u_1 u_2

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate
namespace Problem336AdditiveD139

lemma stronglyRayleighCountable_of_finiteMarginal {I : Type u_1}
    (μ : ProbabilityMeasure (I → Bool))
    (h : ∀ S : Finset I, S.Nonempty → StronglyRayleighFinite (finiteMarginal μ S)) :
    StronglyRayleighCountable μ := by
  classical
  intro S z hz
  by_cases hS : S.Nonempty
  · rw [← finiteGeneratingValue_finiteMarginal]
    exact h S hS z hz
  · have hS' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rw [marginalGeneratingValue_empty]
    exact one_ne_zero

lemma stronglyRayleighCountable_iff_finiteMarginal {I : Type u_2}
    (μ : ProbabilityMeasure (I → Bool)) :
    StronglyRayleighCountable μ ↔
      ∀ S : Finset I, StronglyRayleighFinite (finiteMarginal μ S) := by
  constructor
  · intro h S z hz
    rw [finiteGeneratingValue_finiteMarginal]
    exact h S z hz
  · intro h
    exact stronglyRayleighCountable_of_finiteMarginal μ (fun S _ => h S)

lemma isDeterminantalLaw_stronglyRayleighCountable_of_finite
    {I : Type u} (K : I → I → ℂ) (μ : ProbabilityMeasure (I → Bool))
    (hfinite : ∀ (F : Type u) [Fintype F] [Nonempty F] (L : F → F → ℂ),
      PositiveContractionFinite L → ∀ ν : ProbabilityMeasure (F → Bool),
        IsFiniteDeterminantalLaw ν L → StronglyRayleighFinite ν)
    (hK : PositiveContractionKernel K) (hμ : IsDeterminantalLaw μ K) :
    StronglyRayleighCountable μ := by
  apply stronglyRayleighCountable_of_finiteMarginal μ
  intro S hS
  let : Nonempty S := hS.to_subtype
  exact hfinite S (fun i j : S => K i.1 j.1)
    (positiveContractionFinite_restrict K hK S) (finiteMarginal μ S)
    (finiteMarginal_isDeterminantal hμ S)

end Problem336AdditiveD139

end

end OAI
