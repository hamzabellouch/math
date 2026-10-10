import OAI.NumberTheory.Ostmann.Construction.GroupedPrimePair

namespace OAI

/-! # The existing supported comparison specialized to words of actual primes -/

namespace Ostmann
open scoped Classical SchwartzMap FourierTransform

def primeWordEmbedding {I K : Type*} (words : I → List K) : I → List (Option K) :=
  fun i => (words i).map some

theorem primeWordEmbedding_unfixed {I K : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List K) :
    (expandedSchedulePrimes role n n []
      (fun i => (primeWordEmbedding words i).map Sum.inl)).Coordinates (· ≠ none) := by
  apply expandedSchedulePrimes_unfixed
  intro i _ v hv
  simp only [primeWordEmbedding, List.map_map, List.mem_map] at hv
  obtain ⟨a, _, rfl⟩ := hv
  exact ⟨a, rfl⟩

theorem primeWordEmbedding_hasVariable {I K : Type*} [Fintype I]
    (words : I → List K) :
    ∀ c ∈ atomPairChecks (primeWordEmbedding words), c.HasVariable := by
  apply atomPairChecks_hasVariable
  intro i j hi
  simp only [primeWordEmbedding, List.mem_map, Option.some_ne_none, and_false, exists_false] at hi

theorem groupedFullCoprimeFourierWeight_primeWordEmbedding {I K : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List K)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (p : K → ℕ) :
    groupedFullCoprimeFourierWeight role n (primeWordEmbedding words) childBound pivotBound
      ranges ψ X lo hi t (fixedPivotPrimeValues 1 p) =
    groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t p := by
  rw [groupedFullCoprimeFourierWeight_atom, groupedFullCoprimeFourierWeight_atom]
  congr 1
  funext i
  simp only [primeWordEmbedding, List.map_map, Function.comp_def, fixedPivotPrimeValues]

end Ostmann

end OAI
