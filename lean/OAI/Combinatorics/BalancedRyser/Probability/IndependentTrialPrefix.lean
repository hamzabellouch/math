import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrialKernel
import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrials

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

variable {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {A : Fin T → Type*} [∀ i, MeasurableSpace (A i)]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : ∀ i, Ω → A i}

omit [IsProbabilityMeasure μ] in

theorem prefixFiltration_eq_comap (hξ : ∀ i, Measurable (ξ i)) (n : ℕ) :
    prefixFiltration ξ hξ n =
      (inferInstance : MeasurableSpace (∀ i : prefixIndices T n, A i)).comap
        (fun ω (i : prefixIndices T n) => ξ i ω) := by
  change ((MeasurableSpace.pi.comap (prefixIndices T n).restrict).comap
    (trialVector ξ)) = _
  rw [MeasurableSpace.comap_comp]
  rfl

theorem doobProcess_eq_future_average
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (F : (∀ i, A i) → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun ω => F (trialVector ξ ω)) μ) (n : ℕ) :
    doobProcess ξ hξ (fun ω => F (trialVector ξ ω)) μ n =ᵐ[μ]
      fun ω => ∫ y, F ((MeasurableEquiv.piEquivPiSubtypeProd A
        (fun i => i ∈ prefixIndices T n)).symm
          ((fun i : prefixIndices T n => ξ i ω), y))
        ∂(μ.map (fun ω (i : {i // i ∉ prefixIndices T n}) => ξ i ω)) := by
  rw [doobProcess, prefixFiltration_eq_comap]
  exact condExp_independent_family (fun i => i ∈ prefixIndices T n)
    hξ hind F hF.stronglyMeasurable hFi

end Balanced.IndependentTrials

end OAI
