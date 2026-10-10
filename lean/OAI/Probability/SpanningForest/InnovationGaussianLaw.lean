import OAI.Probability.SpanningForest.InnovationSubdivision
import OAI.Probability.SpanningForest.InnovationLawIdentification

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Problem336.InnovationGaussianLaw

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [mE : MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem hasLaw_and_indep_of_gaussian_recurrences
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure E) [IsFiniteMeasure ν]
    (X : Ω → E) (hX : Measurable X) (past : MeasurableSpace Ω)
    (hpast : past ≤ mΩ) (T : ℝ) (hT : 0 ≤ T)
    (v C : E → ℝ) (hv : ∀ θ, 0 ≤ v θ)
    (hchar : ∀ θ, charFun ν θ = (Real.exp (-T * v θ) : ℂ))
    (μ : Set Ω → E → ℕ → ℕ → ℂ)
    (hinit : ∀ A, MeasurableSet[past] A → ∀ θ n,
      μ A θ n 0 = ((P A).toReal : ℂ))
    (hfinal : ∀ A, MeasurableSet[past] A → ∀ θ n,
      μ A θ n (n + 1) =
        ∫ ω in A, Complex.exp ((inner ℝ (X ω) θ : ℝ) * Complex.I) ∂P)
    (hstep : ∀ A, MeasurableSet[past] A → ∀ θ,
      ∀ᶠ n : ℕ in atTop, ∀ k < n + 1,
        ‖μ A θ n (k + 1) -
          (Real.exp (-(T / ((n + 1 : ℕ) : ℝ)) * v θ) : ℂ) * μ A θ n k‖ ≤
          C θ * (T / ((n + 1 : ℕ) : ℝ)) * Real.sqrt (T / ((n + 1 : ℕ) : ℝ))) :
    HasLaw X ν P ∧ Indep (MeasurableSpace.comap X mE) past P := by
  let : MeasurableSpace Ω := mΩ
  apply InnovationLawIdentification.hasLaw_and_indep_of_restricted_integral
    P ν X hX past hpast
  intro A hA θ
  have heq := InnovationSubdivision.gaussian_identity_of_subdivision_recurrences
    (∫ ω in A, Complex.exp ((inner ℝ (X ω) θ : ℝ) * Complex.I) ∂P)
    ((P A).toReal : ℂ) (μ A θ) (C θ) T (v θ) hT (hv θ)
    (hinit A hA θ) (hfinal A hA θ) (hstep A hA θ)
  simpa only [hchar θ, mul_comm] using heq

end Problem336.InnovationGaussianLaw

end

end OAI
