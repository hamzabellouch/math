import OAI.NumberTheory.Jacobsthal.Probability.FiniteHistoryPairLaw

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.FinitePairOccurrence
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FiniteHistoryTransport FiniteHistoryOccurrence FiniteHistoryPairLaw

variable {X : Type*} [MeasurableSpace X]

noncomputable def pairOccurrence (E : Set (X×X)) (N : ℕ) : Set (Hist X N) :=
  ⋃ j : Fin N,(fun h => adjacentPair N h j) ⁻¹' E

theorem pairOccurrence_measurable {E : Set (X×X)} (hE : MeasurableSet E) (N : ℕ) :
    MeasurableSet (pairOccurrence E N) := MeasurableSet.iUnion (fun j => (adjacentPair_measurable N j) hE)

theorem pair_occurrence_lintegral_bound (K : Kernel X X) [IsMarkovKernel K]
    {E : Set (X×X)} (hE : MeasurableSet E) (N : ℕ) (h₀ : Hist X 0) :
    pathKernel K N h₀ (pairOccurrence E N) ≤
      ∫⁻ h,∑ j : Fin N,pairProbability K E (atIndex N h j.castSucc) ∂pathKernel K N h₀ := by
  apply (measure_iUnion_fintype_le _ (fun j : Fin N => (fun h => adjacentPair N h j) ⁻¹' E)).trans_eq
  simp_rw [adjacent_pair_probability K hE N h₀]
  symm
  apply lintegral_finsetSum
  intro j _
  have hc : Measurable (fun h : Hist X N => atIndex N h j.castSucc) := measurable_pi_apply _
  exact (pairProbability_measurable K hE).comp hc

theorem pair_occurrence_of_budget (K : Kernel X X) [IsMarkovKernel K]
    {E : Set (X×X)} (hE : MeasurableSet E) (N : ℕ) (h₀ : Hist X 0)
    (g : X → ℝ) (hg : ∀ x,0 ≤ g x) (C : ℝ)
    (hrow : ∀ x,pairProbability K E x ≤ ENNReal.ofReal (g x))
    (hbudget : ∀ᵐ h ∂pathKernel K N h₀,(∑ j : Fin N,g (atIndex N h j.castSucc)) ≤ C) :
    pathKernel K N h₀ (pairOccurrence E N) ≤ ENNReal.ofReal C := by
  calc
    _ ≤ ∫⁻ h,∑ j : Fin N,pairProbability K E (atIndex N h j.castSucc) ∂pathKernel K N h₀ :=
      pair_occurrence_lintegral_bound K hE N h₀
    _ ≤ ∫⁻ h,ENNReal.ofReal (∑ j : Fin N,g (atIndex N h j.castSucc)) ∂pathKernel K N h₀ := by
      apply lintegral_mono
      intro h
      change (∑ j : Fin N,pairProbability K E (atIndex N h j.castSucc)) ≤
        ENNReal.ofReal (∑ j : Fin N,g (atIndex N h j.castSucc))
      rw [ENNReal.ofReal_sum_of_nonneg (fun (j : Fin N) (_ : j ∈ Finset.univ) => hg (atIndex N h j.castSucc))]
      exact Finset.sum_le_sum (fun j _ => hrow _)
    _ ≤ ∫⁻ _h : Hist X N,ENNReal.ofReal C ∂pathKernel K N h₀ :=
      lintegral_mono_ae (hbudget.mono (fun h hh => ENNReal.ofReal_le_ofReal hh))
    _ = _ := by simp

theorem pair_occurrence_of_uniform_row (K : Kernel X X) [IsMarkovKernel K]
    {E : Set (X×X)} (hE : MeasurableSet E) (N : ℕ) (h₀ : Hist X 0)
    {A : ℝ} (hA : 0 ≤ A) (hrow : ∀ x,pairProbability K E x ≤ ENNReal.ofReal A) :
    pathKernel K N h₀ (pairOccurrence E N) ≤ ENNReal.ofReal ((N:ℝ)*A) := by
  apply pair_occurrence_of_budget K hE N h₀ (fun _ => A) (fun _ => hA) ((N:ℝ)*A) hrow
  exact Filter.Eventually.of_forall (fun _ => by simp)
end NumberTheoryLean.FinitePairOccurrence


end Erdos970

end OAI
