import OAI.Probability.InvariantIsing.Arrays.TensorMinimumPressure

namespace OAI

/-! Choose the actual pressure minimizers simultaneously at all positive
physical sizes. This keeps one deterministic sequence for telescoping. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem tensor_zero_field_minimizing_sequence
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (m depth : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents depth b)
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    (hμ : ∀ N, (μ N).IsMulLeftInvariant)
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N)) :
    ∃ u : (N : ℕ) → Fin N → ℝ, ∃ v : ℕ → Fin m → ℝ,
      (∀ N j, u N j ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ N a, v N a ∈ Set.Icc (1 : ℝ) 2) ∧
      ∀ N, 3≤N → ∀ u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
        (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b
          (fun _ => 0) (u N) (v N) ≤
        tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b (fun _ => 0) u' v' := by
  have hex N : ∃ u : Fin N → ℝ, ∃ v : Fin m → ℝ,
      (∀ j, u j ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ a, v a ∈ Set.Icc (1 : ℝ) 2) ∧
      ∀ (_hN : 3≤N) u' v', (∀ j, u' j ∈ Set.Icc (1 : ℝ) 2) →
        (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b
          (fun _ => 0) u v ≤
        tensorPerturbationObjective (μ N) (eig N) (c N) (I N) 1 depth b (fun _ => 0) u' v' := by
    by_cases hN : 3≤N
    · obtain ⟨u,v,hu,hv,hm⟩ := tensorPerturbationObjective_exists_minimum hhaar hgauss hN
        (μ N) (hμ N) (eig N) (c N) (I N) 1 depth b hb (fun _ => 0) monotone_const le_rfl
      exact ⟨u,v,hu,hv,fun _ => hm⟩
    · exact ⟨fun _ => 3/2,fun _ => 3/2,fun _ => by norm_num,
        fun _ => by norm_num,fun h => (hN h).elim⟩
  choose u v hu hv hm using hex
  exact ⟨u,v,hu,hv,hm⟩

end InvariantIsing

end

end OAI
