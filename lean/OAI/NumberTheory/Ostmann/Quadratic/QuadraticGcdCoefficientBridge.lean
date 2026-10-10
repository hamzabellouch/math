import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdReduction
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOffDiagonalBound

namespace OAI

/-! # The actual gcd-removal coefficients for all three divisor corrections -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_gcd_coefficient_reindex {N D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs N D,
      v z.1 * conj (w z.2) * F (quadraticPairKernel z.1 z.2)) =
    ∑ z ∈ quadraticGcdPairs (N / D) 1,
      quadraticDivisibilityCoeff D v z.1 * conj (quadraticDivisibilityCoeff D w z.2) * F (z.1 * z.2) := by
  rw [quadratic_gcd_pair_reindex (N := N) hD ho
    (fun s t => v s * conj (w t) * F (quadraticPairKernel s t))]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨_, hg⟩ := Finset.mem_filter.mp hz
  rw [quadraticPairKernel_mul_coprime hD.ne_zero hg]
  unfold quadraticDivisibilityCoeff
  by_cases hs : D.Coprime z.1
  · by_cases ht : D.Coprime z.2
    · rw [ite_eq_left ⟨hs, ht⟩, ite_eq_left hs, ite_eq_left ht]
    · rw [ite_eq_right (fun h => ht h.2), ite_eq_left hs, ite_eq_right ht]
      simp
  · rw [ite_eq_right (fun h => hs h.1), ite_eq_right hs]
    simp

theorem quadratic_gcd_coefficient_energy {N D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v : ℕ → ℂ) :
    quadraticSieveEnergy (N / D) (quadraticDivisibilityCoeff D v) ≤ quadraticSieveEnergy N v := by
  rw [quadraticSieveEnergy_divisibility D N hD ho]
  apply Finset.sum_le_sum
  intro n _
  dsimp only
  split_ifs
  · rfl
  · simp

theorem quadratic_gcd_coefficient_lower {R D : ℕ} (hD : 0 < D) (v : ℕ → ℂ)
    (hv : ∀ n < R, v n = 0) {n : ℕ} (hn : n < R / D) :
    quadraticDivisibilityCoeff D v n = 0 := by
  have hmul : D * n < R := by
    have h₁ := Nat.mul_lt_mul_of_pos_left hn hD
    have h₂ := Nat.mul_div_le R D
    nlinarith
  simp [quadraticDivisibilityCoeff, hv _ hmul]

theorem quadratic_gcd_coefficient_product (D : ℕ) (v w : ℕ → ℂ) (s t : ℕ) :
    quadraticDivisibilityCoeff D v s * conj (quadraticDivisibilityCoeff D w t) =
      if D.Coprime (s * t) then v (D * s) * conj (w (D * t)) else 0 := by
  unfold quadraticDivisibilityCoeff
  by_cases hs : D.Coprime s
  · by_cases ht : D.Coprime t
    · rw [ite_eq_left hs, ite_eq_left ht, ite_eq_left (hs.mul_right ht)]
    · have hn : ¬ D.Coprime (s * t) := fun h => ht (Nat.coprime_mul_iff_right.mp h).2
      rw [ite_eq_left hs, ite_eq_right ht, ite_eq_right hn]
      simp
  · have hn : ¬ D.Coprime (s * t) := fun h => hs (Nat.coprime_mul_iff_right.mp h).1
    rw [ite_eq_right hs, ite_eq_right hn]
    simp

theorem quadratic_coprime_kernel_sum (N : ℕ) (v w : ℕ → ℂ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs N 1, v z.1 * conj (w z.2) * F (z.1 * z.2)) =
      ∑ s ∈ oddSquarefreeRange N, ∑ t ∈ oddSquarefreeRange N,
        if s.Coprime t then v s * conj (w t) * F (s * t) else 0 := by
  unfold quadraticGcdPairs
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]

theorem quadratic_gcd_coprime_correction {N D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs N D,
      v z.1 * conj (w z.2) * F (quadraticPairKernel z.1 z.2)) =
      ∑ s ∈ oddSquarefreeRange (N / D), ∑ t ∈ oddSquarefreeRange (N / D),
        if s.Coprime t then
          quadraticDivisibilityCoeff D v s * conj (quadraticDivisibilityCoeff D w t) * F (s * t)
        else 0 := by
  rw [quadratic_gcd_coefficient_reindex hD ho, quadratic_coprime_kernel_sum]

end Ostmann

end OAI
