import OAI.Probability.InvariantIsing.Cavity.OffsetEnvelopeLower

namespace OAI

/-! Simultaneous actual minima at every repetition count. The small
unused dimensions carry bounded placeholders. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def offsetRepeatedPriorObjective {m n r₀ : ℕ}
    (μ : (N : ℕ) → Measure (SpecialOrthogonal N))
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) (K : ℕ)
    (u : Fin (r₀+K*n) → ℝ) (v : Fin m → ℝ) : ℝ :=
  priorPerturbationObjective (μ (r₀+K*n))
    (restrictedZeroTreePrior (offsetBlockConstraint K R C)
      (offsetBlockConstraint_nonempty R hR C hC))
    (eig (r₀+K*n)) (c (r₀+K*n)) (I (r₀+K*n)) 1 (fun _ => 0) u v

theorem offset_prior_minimizing_sequence
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {m n r₀ : ℕ} (μ : (N : ℕ) → Measure (SpecialOrthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    (hμ : ∀ N, (μ N).IsMulLeftInvariant)
    (eig c : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) :
    ∃ (u : (K : ℕ) → Fin (r₀+K*n) → ℝ) (v : ℕ → Fin m → ℝ),
      (∀ K i, u K i ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ K a, v K a ∈ Set.Icc (1 : ℝ) 2) ∧
      ∀ K, 3 ≤ r₀+K*n → ∀ u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
        (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        offsetRepeatedPriorObjective μ eig c I R hR C hC K (u K) (v K) ≤
          offsetRepeatedPriorObjective μ eig c I R hR C hC K u' v' := by
  have hex K : ∃ (u : Fin (r₀+K*n) → ℝ) (v : Fin m → ℝ),
      (∀ i, u i ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ a, v a ∈ Set.Icc (1 : ℝ) 2) ∧
      (3 ≤ r₀+K*n → ∀ u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
        (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        offsetRepeatedPriorObjective μ eig c I R hR C hC K u v ≤
          offsetRepeatedPriorObjective μ eig c I R hR C hC K u' v') := by
    by_cases hK : 3 ≤ r₀+K*n
    · let π : Measure (Spin (r₀+K*n) × LabeledLeaf 0) :=
        restrictedZeroTreePrior (offsetBlockConstraint K R C) (offsetBlockConstraint_nonempty R hR C hC)
      let : IsProbabilityMeasure π := restrictedZeroTreePrior_probability _ _
      obtain ⟨u,v,hu,hv,hmin⟩ := priorPerturbationObjective_exists_minimum hhaar hgauss hK
        (μ (r₀+K*n)) (hμ (r₀+K*n)) π (eig (r₀+K*n)) (c (r₀+K*n)) (I (r₀+K*n)) 1
        (fun _ => 0) monotone_const le_rfl
      exact ⟨u,v,hu,hv,fun _ => hmin⟩
    · exact ⟨fun _ => 1,fun _ => 1,fun _ => by norm_num,fun _ => by norm_num,
        fun h => (hK h).elim⟩
  choose u v hu hv hmin using hex
  exact ⟨u,v,hu,hv,hmin⟩

end InvariantIsing

end

end OAI
