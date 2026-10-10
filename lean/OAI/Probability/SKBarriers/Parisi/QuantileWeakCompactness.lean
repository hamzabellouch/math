import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarAtomic

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

def quantileProbability (k : ℕ) (Q : Fin (k+1) → ℝ) : ProbabilityMeasure ℝ :=
  ⟨quantileAtomLaw k Q,quantileAtomLaw_probability k Q⟩

theorem quantileProbability_weak_subsequence (K : ℕ → ℕ)
    (A : (n : ℕ) → Fin (K n+1) → ℝ)
    (hA : ∀ n j, A n j ∈ Set.Icc 0 1) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Set.Icc 0 1) = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => quantileProbability (K (φ n)) (A (φ n))) atTop (𝓝 μ) := by
  have hc : IsCompact {μ : ProbabilityMeasure ℝ | ∀ _n : ℕ, μ (Set.Icc (0:ℝ) 1)ᶜ ≤ 0} :=
    isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
      (u := fun _ => (0:NNReal)) (K := fun _ => Set.Icc (0:ℝ) 1)
      tendsto_const_nhds (fun _ => isCompact_Icc) (Or.inl inferInstance)
  have hm (n : ℕ) : quantileProbability (K n) (A n) ∈
      {μ : ProbabilityMeasure ℝ | ∀ _n : ℕ, μ (Set.Icc (0:ℝ) 1)ᶜ ≤ 0} := by
    intro _
    apply le_of_eq
    apply (ProbabilityMeasure.null_iff_toMeasure_null _ _).mpr
    exact (prob_compl_eq_zero_iff measurableSet_Icc).mpr
      (quantileAtomLaw_supported (K n) (A n) (hA n))
  obtain ⟨μ,hμ,φ,hφ,ht⟩ := hc.tendsto_subseq hm
  refine ⟨μ,?_,φ,hφ,ht⟩
  apply (prob_compl_eq_zero_iff measurableSet_Icc).mp
  exact (ProbabilityMeasure.null_iff_toMeasure_null μ _).mp (le_antisymm (hμ 0) bot_le)

end SK.Analytic

end
end

end

end OAI
