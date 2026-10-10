import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.Ideal.Span

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W22

open scoped BigOperators

variable {k σ ι : Type*} [CommRing k]

noncomputable def parameterCombination (s : Finset ι) (c : ι → k)
    (f : ι → MvPolynomial σ k) : MvPolynomial σ k :=
  ∑ i ∈ s, MvPolynomial.C (c i) * f i

theorem parameterCombination_totalDegree_le (s : Finset ι) (c : ι → k)
    (f : ι → MvPolynomial σ k) {d : ℕ}
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ d) :
    (parameterCombination s c f).totalDegree ≤ d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  calc
    (MvPolynomial.C (c i) * f i).totalDegree ≤
        (MvPolynomial.C (c i) : MvPolynomial σ k).totalDegree + (f i).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (f i).totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
    _ ≤ d := hf i hi

theorem parameterCombination_mem (s : Finset ι) (c : ι → k)
    (f : ι → MvPolynomial σ k) (J : Ideal (MvPolynomial σ k))
    (hf : ∀ i ∈ s, f i ∈ J) : parameterCombination s c f ∈ J := by
  apply J.sum_mem
  intro i hi
  exact J.mul_mem_left _ (hf i hi)

theorem parameterCandidates_span_le {κ : Type*} (s : Finset ι) (c : κ → ι → k)
    (f : ι → MvPolynomial σ k) (J : Ideal (MvPolynomial σ k))
    (hf : ∀ i ∈ s, f i ∈ J) :
    Ideal.span (Set.range (fun j => parameterCombination s (c j) f)) ≤ J := by
  apply Ideal.span_le.mpr
  rintro p ⟨j, rfl⟩
  exact parameterCombination_mem s (c j) f J hf

end WeightedTorusJets.W22

end

end SiegelZeros

end OAI
