import OAI.InformationTheory.Entanglement.PhysicalExecutionStep

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder MeasureTheory
open ContinuousLinearMap MeasureTheory ProbabilityTheory Filter
namespace SecretKey
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι κ X : Type*} [MeasurableSpace X]

theorem physical_chronological_prefixes (b : HilbertBasis ι ℂ H) (d : HilbertBasis κ ℂ K)
    (W : (n : ℕ)→PositiveHilbertMeasure (Fin n→X) (HilbertTensor H K) (tensorHilbertBasis b d))
    [∀ n, IsProbabilityMeasure (W n).traceMeasure]
    (ρ : (n : ℕ)→(Fin n→X)→DensityOperator b)
    (σ : (n : ℕ)→(Fin n→X)→DensityOperator d)
    (P : (n : ℕ)→Kernel (Fin n→X) X) [∀ n, IsMarkovKernel (P n)]
    (hm : ∀ n x y, Measurable (fun h => inner ℂ x ((densityTensor b d (ρ n h) (σ n h)).val.val y)))
    (hzero : IsWeakDensity (tensorHilbertBasis b d) (W 0) (W 0).traceMeasure
      (fun h => densityTensor b d (ρ 0 h) (σ 0 h)))
    (hstep : ∀ n, PhysicalExecutionStep b d (W n)
       ((W (n+1)).mapRecord (historyStepEquiv X n) (historyStepEquiv X n).measurable)
       (ρ n) (σ n) (ρ (n+1) ∘ (historyStepEquiv X n).symm)
       (σ (n+1) ∘ (historyStepEquiv X n).symm) (P n)) :
    (∀ n, IsWeakDensity (tensorHilbertBasis b d) (W n) (W n).traceMeasure
      (fun h => densityTensor b d (ρ n h) (σ n h))) ∧
    (∀ n, (W (n+1)).traceMeasure.map (historyStepEquiv X n)=(W n).traceMeasure ⊗ₘ P n) := by
  have hs n (hd : IsWeakDensity (tensorHilbertBasis b d) (W n) (W n).traceMeasure
      (fun h => densityTensor b d (ρ n h) (σ n h))) :=
    physical_execution_step b d (W n)
      ((W (n+1)).mapRecord (historyStepEquiv X n) (historyStepEquiv X n).measurable)
      (ρ n) (σ n) (ρ (n+1) ∘ (historyStepEquiv X n).symm)
      (σ (n+1) ∘ (historyStepEquiv X n).symm) (P n)
      (hm n) (fun x y => (hm (n+1) x y).comp (historyStepEquiv X n).symm.measurable) hd (hstep n)
  have hd n : IsWeakDensity (tensorHilbertBasis b d) (W n) (W n).traceMeasure
      (fun h => densityTensor b d (ρ n h) (σ n h)) := by
    induction n with
    | zero => exact hzero
    | succ n ih =>
      obtain ⟨hk,hpost⟩ := hs n ih
      apply weakDensity_of_step (tensorHilbertBasis b d) (W (n+1)) (W (n+1)).traceMeasure
        (fun h => densityTensor b d (ρ (n+1) h) (σ (n+1) h)) (hm (n+1))
      change IsWeakDensity (tensorHilbertBasis b d)
        ((W (n+1)).mapRecord (historyStepEquiv X n) (historyStepEquiv X n).measurable)
        (((W (n+1)).mapRecord (historyStepEquiv X n) (historyStepEquiv X n).measurable).traceMeasure) _
      rw [hk]
      exact hpost
  exact ⟨hd,fun n => (hs n (hd n)).1⟩

theorem complete_history_kernel_of_prefixes [StandardBorelSpace X] [Nonempty X]
    (W : (n : ℕ)→Measure (Fin n→X))
    (P : (n : ℕ)→Kernel (Fin n→X) X)
    (hs : ∀ n, (W (n+1)).map (historyStepEquiv X n)=W n ⊗ₘ P n)
    (ν : Measure (ℕ→X))
    (hfull : ∀ n, ν.map (recordPrefix n)=W n) :
    ∀ n, ν.map (fun x => (recordPrefix n x,x n))=ν.map (recordPrefix n) ⊗ₘ P n := by
  intro n
  have he : (fun x : ℕ→X => (recordPrefix n x,x n))=
      (historyStepEquiv X n) ∘ recordPrefix (n+1) := rfl
  rw [he,← Measure.map_map (historyStepEquiv X n).measurable (recordPrefix_measurable (n+1)),
    hfull (n+1),hs n,hfull n]

end SecretKey

end

end OAI
