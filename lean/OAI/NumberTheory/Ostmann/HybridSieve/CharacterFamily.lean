import OAI.NumberTheory.Ostmann.HybridSieve.IntervalSieve

namespace OAI

open scoped Classical
namespace Ostmann.HybridSieve

abbrev PrimitiveFamily (Q : ℕ) :=
  (q : Fin Q) × {χ : DirichletCharacter ℂ (q.val+1) // χ.IsPrimitive}

noncomputable def familyWeight {Q : ℕ} (i : PrimitiveFamily Q) : ℝ :=
  ((i.1.val+1:ℕ):ℝ) / ((i.1.val+1).totient:ℝ)

noncomputable def familyValue {Q : ℕ} (i : PrimitiveFamily Q) (n : ℕ) : ℂ :=
  i.2.val (n : ZMod (i.1.val+1))

lemma familyWeight_nonneg {Q : ℕ} (i : PrimitiveFamily Q) : 0 ≤ familyWeight i := by
  unfold familyWeight
  positivity

lemma family_interval_sieve (s : Finset ℕ) (a : ℕ → ℂ) (A M Q : ℕ)
    (ha : ∀ n ∈ s, a n ≠ 0 → A ≤ n ∧ n < A+M) :
    (∑ i : PrimitiveFamily Q, familyWeight i * ‖∑ n ∈ s, a n * familyValue i n‖^2) ≤
      ((M:ℝ)+(Q:ℝ)^2*(harmonic (Q^2):ℝ)) * ∑ n ∈ s, ‖a n‖^2 := by
  rw [Fintype.sum_sigma]
  simp only [familyWeight, familyValue, ← Finset.mul_sum]
  convert interval_multiplicative_large_sieve s a A M Q ha using 1
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  symm
  exact Finset.sum_subtype _ (by simp) _

end Ostmann.HybridSieve

end OAI
