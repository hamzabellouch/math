import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMainCoefficientBound

namespace OAI

/-! # Finite expansion of the original main terms by their integer coefficients -/

namespace Ostmann

open scoped Classical BigOperators

private theorem coefficient_functional (A B : Finset ℕ) (i : ℕ → ℕ → ℕ)
    (c : ℕ → ℤ) (H : ℕ) (F : ℕ → ℂ)
    (hi : ∀ a ∈ A, ∀ b ∈ B, i a b ∈ Finset.Icc 1 H) :
    (∑ w ∈ Finset.Icc 1 H,
      ((∑ a ∈ A, ∑ b ∈ B, if i a b = w then c a else 0 : ℤ) : ℂ) * F w) =
      ∑ a ∈ A, (c a : ℂ) * ∑ b ∈ B, F (i a b) := by
  simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_eq_single_of_mem (i a b) (hi a ha b hb)]
  · simp
  · intro w _ hw
    simp [Ne.symm hw]

 theorem quadraticMainAlpha_functional {D K : ℕ} (hD : 0 < D) (F : ℕ → ℂ) :
    (∑ w ∈ Finset.Icc 1 (K * D ^ 2), (quadraticMainAlpha D K w : ℂ) * F w) =
      ∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) *
        ∑ b ∈ oddSquarefreeRange K, F (e * b) := by
  apply coefficient_functional
  intro e he b hb
  obtain ⟨hbr, _, _⟩ := Finset.mem_filter.mp hb
  have hepos := Nat.pos_of_mem_divisors he
  have heD := Nat.le_of_dvd hD (Nat.dvd_of_mem_divisors he)
  apply Finset.mem_Icc.mpr
  refine ⟨Nat.mul_pos hepos (Finset.mem_Icc.mp hbr).1, ?_⟩
  have hDs : D ≤ D ^ 2 := by nlinarith
  calc
    e * b ≤ D * K := Nat.mul_le_mul heD (Finset.mem_Icc.mp hbr).2
    _ ≤ D ^ 2 * K := Nat.mul_le_mul_right K hDs
    _ = K * D ^ 2 := Nat.mul_comm _ _

 theorem quadraticMainBeta_functional {D K : ℕ} (hD : 0 < D) (F : ℕ → ℂ) :
    (∑ w ∈ Finset.Icc 1 (K * D ^ 2), (quadraticMainBeta D K w : ℂ) * F w) =
      ∑ u ∈ D.divisors, (ArithmeticFunction.moebius u : ℂ) *
        ∑ v ∈ (oddSquarefreeRange K).filter (D.Coprime ·), F (u ^ 2 * v) := by
  apply coefficient_functional
  intro u hu v hv
  obtain ⟨hv, _⟩ := Finset.mem_filter.mp hv
  obtain ⟨hvr, _, _⟩ := Finset.mem_filter.mp hv
  have hupos := Nat.pos_of_mem_divisors hu
  have huD := Nat.le_of_dvd hD (Nat.dvd_of_mem_divisors hu)
  apply Finset.mem_Icc.mpr
  refine ⟨Nat.mul_pos (pow_pos hupos 2) (Finset.mem_Icc.mp hvr).1, ?_⟩
  calc
    u ^ 2 * v ≤ D ^ 2 * K := Nat.mul_le_mul (Nat.pow_le_pow_left huD 2)
      (Finset.mem_Icc.mp hvr).2
    _ = K * D ^ 2 := Nat.mul_comm _ _

 theorem quadraticMainGamma_functional {D K : ℕ} (hD : 0 < D) (F : ℕ → ℂ) :
    (∑ w ∈ Finset.Icc 1 (K * D ^ 2), (quadraticMainGamma D K w : ℂ) * F w) =
      (∑ e ∈ D.divisors, (ArithmeticFunction.moebius e : ℂ) *
        ∑ b ∈ oddSquarefreeRange K, F (e * b)) -
      ∑ u ∈ D.divisors, (ArithmeticFunction.moebius u : ℂ) *
        ∑ v ∈ (oddSquarefreeRange K).filter (D.Coprime ·), F (u ^ 2 * v) := by
  simp only [quadraticMainGamma, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  rw [quadraticMainAlpha_functional hD, quadraticMainBeta_functional hD]

end Ostmann

end OAI
