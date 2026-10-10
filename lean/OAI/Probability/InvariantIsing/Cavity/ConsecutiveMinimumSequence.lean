import OAI.Probability.InvariantIsing.Cavity.ConsecutiveEnvelopeLower

namespace OAI

/-! Simultaneous actual minima at every repetition count. The small
unused dimensions carry bounded placeholders. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def repeatedPriorObjective {m n : ℕ}
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N))
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (C : Finset (Spin n)) (hC : C.Nonempty) (K : ℕ)
    (u : Fin (K*n) → ℝ) (v : Fin m → ℝ) : ℝ :=
  priorPerturbationObjective (μ (K*n))
    (restrictedZeroTreePrior (consecutiveBlockConstraint n K C)
      (consecutiveBlockConstraint_nonempty C hC))
    (eig (K*n)) (c (K*n)) (I (K*n)) 1 (fun _ => 0) u v

theorem repeated_prior_minimizing_sequence
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {m n : ℕ} (μ : (N : ℕ) → Measure (SpecialOrthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    (hμ : ∀ N, (μ N).IsMulLeftInvariant)
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (C : Finset (Spin n)) (hC : C.Nonempty) :
    ∃ (u : (K : ℕ) → Fin (K*n) → ℝ) (v : ℕ → Fin m → ℝ),
      (∀ K i, u K i ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ K a, v K a ∈ Set.Icc (1 : ℝ) 2) ∧
      ∀ K, 3 ≤ K*n → ∀ u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
        (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        repeatedPriorObjective μ eig c I C hC K (u K) (v K) ≤
          repeatedPriorObjective μ eig c I C hC K u' v' := by
  have hex K : ∃ (u : Fin (K*n) → ℝ) (v : Fin m → ℝ),
      (∀ i, u i ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ a, v a ∈ Set.Icc (1 : ℝ) 2) ∧
      (3 ≤ K*n → ∀ u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
        (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        repeatedPriorObjective μ eig c I C hC K u v ≤
          repeatedPriorObjective μ eig c I C hC K u' v') := by
    by_cases hK : 3 ≤ K*n
    · let π : Measure (Spin (K*n) × LabeledLeaf 0) :=
        restrictedZeroTreePrior (consecutiveBlockConstraint n K C) (consecutiveBlockConstraint_nonempty C hC)
      let : IsProbabilityMeasure π := restrictedZeroTreePrior_probability _ _
      obtain ⟨u,v,hu,hv,hmin⟩ := priorPerturbationObjective_exists_minimum hhaar hgauss hK
        (μ (K*n)) (hμ (K*n)) π (eig (K*n)) (c (K*n)) (I (K*n)) 1
        (fun _ => 0) monotone_const le_rfl
      exact ⟨u,v,hu,hv,fun _ => hmin⟩
    · exact ⟨fun _ => 1,fun _ => 1,fun _ => by norm_num,fun _ => by norm_num,
        fun h => (hK h).elim⟩
  choose u v hu hv hmin using hex
  exact ⟨u,v,hu,hv,hmin⟩

end InvariantIsing

end

end OAI
