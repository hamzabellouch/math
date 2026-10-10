import OAI.InformationTheory.Entanglement.PhysicalChronology
import OAI.InformationTheory.Entanglement.CausalRealization

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder MeasureTheory unitInterval
open ContinuousLinearMap MeasureTheory ProbabilityTheory Filter Function
namespace SecretKey
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι κ X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]

theorem physical_history_realization (b : HilbertBasis ι ℂ H) (d : HilbertBasis κ ℂ K)
    (role : ℕ→TapeRole) (pub : Set ℕ) (x₀ : X)
    (hsource : ∀ n, role n=.source → n∈pub)
    (W : (n : ℕ)→PositiveHilbertMeasure (Fin n→X) (HilbertTensor H K) (tensorHilbertBasis b d))
    [∀ n, IsProbabilityMeasure (W n).traceMeasure]
    (ρ : (n : ℕ)→(Fin n→X)→DensityOperator b)
    (τ : (n : ℕ)→(Fin n→X)→DensityOperator d)
    (P Q : (n : ℕ)→Kernel (Fin n→X) X)
    [∀ n, IsMarkovKernel (P n)] [∀ n, IsMarkovKernel (Q n)]
    (hlocal : ∀ n, P n=visibleKernel role pub x₀ Q n)
    (hm : ∀ n x y, Measurable (fun h => inner ℂ x ((densityTensor b d (ρ n h) (τ n h)).val.val y)))
    (hzero : IsWeakDensity (tensorHilbertBasis b d) (W 0) (W 0).traceMeasure
      (fun h => densityTensor b d (ρ 0 h) (τ 0 h)))
    (hstep : ∀ n, PhysicalExecutionStep b d (W n)
       ((W (n+1)).mapRecord (historyStepEquiv X n) (historyStepEquiv X n).measurable)
       (ρ n) (τ n) (ρ (n+1) ∘ (historyStepEquiv X n).symm)
       (τ (n+1) ∘ (historyStepEquiv X n).symm) (P n))
    (ν : Measure (ℕ→X)) [IsProbabilityMeasure ν]
    (hfull : ∀ n, ν.map (recordPrefix n)=(W n).traceMeasure) :
    ∃ g : (n : ℕ)→(Fin n→X)→I→X,
      (∀ n, Measurable (uncurry (g n))) ∧
      ν=uniformTapesLaw.map (sampledHistory (causalSampler role pub x₀ g)) ∧
      ∃ hT : Measurable (completeCausalPublic role pub x₀ g),
        CondIndep ((inferInstance : MeasurableSpace (ℕ→X)).comap (completeCausalPublic role pub x₀ g))
          (roleInfo role .alice ⊔ (inferInstance : MeasurableSpace (ℕ→X)).comap (completeCausalPublic role pub x₀ g))
          (roleInfo role .bob ⊔ (inferInstance : MeasurableSpace (ℕ→X)).comap (completeCausalPublic role pub x₀ g))
          hT.comap_le uniformTapesLaw := by
  have hpre := physical_chronological_prefixes b d W ρ τ P hm hzero hstep
  have hν := complete_history_kernel_of_prefixes (fun n => (W n).traceMeasure) P hpre.2 ν hfull
  apply causal_history_realization role pub x₀ hsource Q ν
  intro n
  rw [← hlocal n]
  exact hν n

end SecretKey

end

end OAI
