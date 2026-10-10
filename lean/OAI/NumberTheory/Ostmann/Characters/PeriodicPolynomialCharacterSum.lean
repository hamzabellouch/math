import OAI.NumberTheory.Ostmann.Characters.PolynomialIntegerCharacterSum

namespace OAI

/-! # Keeping the actual small-frequency residue restrictions -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- A bounded function of the residue modulo the frequency modulus is constant
on each progression. It therefore retains the same cancellation bound. -/
theorem periodic_polynomial_integer_character_sum {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (a Q K : ℕ) (ha : 0 < a) (hQ : Q.Coprime (q * r))
    {n t : ℕ} (F : Fin n → ClippedPolynomialFactor) (H : Fin t → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (gate : ZMod Q → ℂ) (hgate : ∀ z, ‖gate z‖ ≤ 1) :
    ‖∑ j : Fin (K * Q), gate ((a + j.val : ℕ) : ZMod Q) *
      supportedPolynomialWeight F H keep ((a + j.val : ℕ) : ℝ) *
      (χ ((a + j.val : ℕ) : ZMod q) * conj (ψ ((a + j.val : ℕ) : ZMod r)))‖ ≤
      (Q : ℝ) * ((3 ^ ((∑ i, (F i).polynomial.derivative.natDegree) +
        ∑ i, (H i).natDegree) : ℕ) *
        (2 * (a : ℝ)⁻¹ * smoothPolynomialBudget F) * (q * r)) := by
  let g : ℕ → ℂ := fun v => supportedPolynomialWeight F H keep (v : ℝ) *
    (χ (v : ZMod q) * conj (ψ (v : ZMod r)))
  simp only [mul_assoc]
  change ‖∑ j : Fin (K * Q), gate ((a + j.val : ℕ) : ZMod Q) * g (a + j.val)‖ ≤ _
  rw [integerProgressionPartition_sum Q K (fun j => gate ((a + j.val : ℕ) : ZMod Q) * g (a + j.val))]
  simp_rw [integerProgressionPartition_value Q K a]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _s : Fin Q, ((3 ^ ((∑ i, (F i).polynomial.derivative.natDegree) +
        ∑ i, (H i).natDegree) : ℕ) *
        (2 * (a : ℝ)⁻¹ * smoothPolynomialBudget F) * (q * r)) := by
      apply Finset.sum_le_sum
      intro s _
      have hmod (j : Fin K) : ((a + s.val + Q * j.val : ℕ) : ZMod Q) = (a + s.val : ℕ) := by
        simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
      simp_rw [hmod]
      rw [← Finset.mul_sum, norm_mul]
      apply (mul_le_mul_of_nonneg_right (hgate _) (norm_nonneg _)).trans
      rw [one_mul]
      have hb := supported_polynomial_character_progression hqr χ ψ hχ (a + s.val) Q K
        (by omega) hQ F H keep
      rw [Fin.sum_univ_eq_sum_range (fun j => g (a + s.val + Q * j)) K]
      apply hb.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (smoothPolynomialBudget_nonneg F)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply inv_anti₀ (by exact_mod_cast ha)
      exact_mod_cast Nat.le_add_right a s.val
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end Ostmann

end OAI
