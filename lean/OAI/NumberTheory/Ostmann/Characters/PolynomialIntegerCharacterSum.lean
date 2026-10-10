import OAI.NumberTheory.Ostmann.Arithmetic.SupportedPolynomialCharacterSum

namespace OAI

/-! # Summing the residue classes of the long-integer interval -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def supportedPolynomialWeight {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (keep : (Fin t → Bool) → Bool) (x : ℝ) : ℂ :=
  (if keep (polynomialSupportCode H x) = true then 1 else 0) *
    (Complex.ofReal (x⁻¹) * smoothPolynomialWeight F x)

/-- This is the bound after summing all frequency-modulus residue classes.
No integer endpoint is removed in the exact rectangular interval. -/
theorem supported_polynomial_integer_character_sum {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (a Q K : ℕ) (ha : 0 < a) (hQ : Q.Coprime (q * r))
    {n t : ℕ} (F : Fin n → ClippedPolynomialFactor) (H : Fin t → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) :
    ‖∑ j : Fin (K * Q), supportedPolynomialWeight F H keep ((a + j.val : ℕ) : ℝ) *
      (χ ((a + j.val : ℕ) : ZMod q) * conj (ψ ((a + j.val : ℕ) : ZMod r)))‖ ≤
      (Q : ℝ) * ((3 ^ ((∑ i, (F i).polynomial.derivative.natDegree) +
        ∑ i, (H i).natDegree) : ℕ) *
        (2 * (a : ℝ)⁻¹ * smoothPolynomialBudget F) * (q * r)) := by
  let g : ℕ → ℂ := fun v => supportedPolynomialWeight F H keep (v : ℝ) *
    (χ (v : ZMod q) * conj (ψ (v : ZMod r)))
  change ‖∑ j : Fin (K * Q), g (a + j.val)‖ ≤ _
  rw [integerProgressionPartition_sum Q K (fun j => g (a + j.val))]
  simp_rw [integerProgressionPartition_value Q K a]
  apply (norm_sum_le _ _).trans
  have hV := smoothPolynomialBudget_nonneg F
  calc
    _ ≤ ∑ _s : Fin Q, ((3 ^ ((∑ i, (F i).polynomial.derivative.natDegree) +
        ∑ i, (H i).natDegree) : ℕ) *
        (2 * (a : ℝ)⁻¹ * smoothPolynomialBudget F) * (q * r)) := by
      apply Finset.sum_le_sum
      intro s _
      have hb := supported_polynomial_character_progression hqr χ ψ hχ (a + s.val) Q K
        (by omega) hQ F H keep
      have he : (∑ j : Fin K, g (a + s.val + Q * j.val)) =
          ∑ j ∈ Finset.range K, g (a + s.val + Q * j) :=
        Fin.sum_univ_eq_sum_range (fun j => g (a + s.val + Q * j)) K
      rw [he]
      change ‖∑ j ∈ Finset.range K,
        (if keep (polynomialSupportCode H ((a + s.val + Q * j : ℕ) : ℝ)) = true then (1 : ℂ) else 0) *
          (Complex.ofReal (((a + s.val + Q * j : ℕ) : ℝ)⁻¹) *
            smoothPolynomialWeight F ((a + s.val + Q * j : ℕ) : ℝ)) *
          (χ ((a + s.val + Q * j : ℕ) : ZMod q) *
            conj (ψ ((a + s.val + Q * j : ℕ) : ZMod r)))‖ ≤ _
      apply hb.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hV
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply inv_anti₀ (by exact_mod_cast ha)
      exact_mod_cast Nat.le_add_right a s.val
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Ostmann

end OAI
