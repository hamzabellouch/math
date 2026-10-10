import OAI.NumberTheory.Ostmann.QuadraticSieve.ComplexJacobiMoment

namespace OAI

/-! # A moment bound uniform over a finite family of coefficient arrays -/

namespace Ostmann

open scoped BigOperators

/-- The array may be chosen separately at each modulus. Thus this estimate
also bounds the pointwise maximum over the family. -/
theorem complex_odd_jacobi_chosen_moment_bound (hB : PublishedBonamiBound)
    {I : Type*} [Fintype I] (P S : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hP : ∀ s ∈ S, s.primeFactors ⊆ P)
    (U M l : ℕ) (hU : ∀ s ∈ S, s ≤ U) (hl : 0 < l)
    (b : I → S → ℂ) (pick : ℕ → I) (E A : ℝ)
    (henergy : ∀ i, (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E)
    (hmass : ∀ i, (∑ s : S, ‖b i s‖) ≤ A) :
    (∑ m ∈ Finset.range M, if Odd m then
        ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0) ≤
      (Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l) *
        ((M : ℝ) * E ^ l + (8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) := by
  classical
  have heach (i : I) :
      (∑ m ∈ Finset.range M, if Odd m then
        ‖∑ s : S, b i s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0) ≤
      (2 : ℝ) ^ (2 * l) * ((M : ℝ) * E ^ l + (8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) := by
    apply (complex_odd_jacobi_even_moment_bound hB P S hS hP U M l hU hl (b i)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (henergy i) l
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (hmass i) (2 * l)
  calc
    _ ≤ ∑ i : I, ∑ m ∈ Finset.range M, if Odd m then
        ‖∑ s : S, b i s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro m hm
      split_ifs with ho
      · exact Finset.single_le_sum
          (f := fun i : I => ‖∑ s : S, b i s * (realJacobi s.val m : ℂ)‖ ^ (2 * l))
          (fun i _ => by positivity) (Finset.mem_univ (pick m))
      · simp
    _ ≤ ∑ _i : I, (2 : ℝ) ^ (2 * l) *
        ((M : ℝ) * E ^ l + (8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l)) :=
      Finset.sum_le_sum (fun i _ => heach i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Ostmann

end OAI
