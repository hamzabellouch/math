import OAI.NumberTheory.Ostmann.Characters.PolynomialCharacterSum
import OAI.NumberTheory.Ostmann.Characters.PolynomialCellSupports

namespace OAI

/-! # The weighted character bound with its actual polynomial support -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def historyWeightRootCuts {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) : Finset ℝ :=
  polynomialRootCuts (Sum.elim (fun i => (F i).polynomial.derivative) H)

theorem historyWeightRootCuts_factor {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (i : Fin n) (x : ℝ)
    (hx : x ∈ (F i).polynomial.derivative.roots) : x ∈ historyWeightRootCuts F H := by
  apply Finset.mem_biUnion.mpr
  exact ⟨Sum.inl i, Finset.mem_univ _, by simpa only [Sum.elim_inl, Multiset.mem_toFinset] using hx⟩

theorem historyWeightRootCuts_support {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (i : Fin t) (x : ℝ) (hx : x ∈ (H i).roots) :
    x ∈ historyWeightRootCuts F H := by
  apply Finset.mem_biUnion.mpr
  exact ⟨Sum.inr i, Finset.mem_univ _, by simpa only [Sum.elim_inr, Multiset.mem_toFinset] using hx⟩

theorem historyWeightRootCuts_card {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) :
    (historyWeightRootCuts F H).card ≤
      (∑ i, (F i).polynomial.derivative.natDegree) + ∑ i, (H i).natDegree := by
  simpa only [historyWeightRootCuts, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using
    polynomialRootCuts_card (Sum.elim (fun i => (F i).polynomial.derivative) H)

theorem supported_polynomial_character_progression {q r : ℕ} [NeZero q] [NeZero r]
    (hqr : q.Coprime r) (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (a M N : ℕ) (ha : 0 < a) (hM : M.Coprime (q * r))
    {n t : ℕ} (F : Fin n → ClippedPolynomialFactor) (H : Fin t → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) :
    ‖∑ j ∈ Finset.range N,
      (if keep (polynomialSupportCode H ((a + M * j : ℕ) : ℝ)) = true then (1 : ℂ) else 0) *
      (Complex.ofReal (((a + M * j : ℕ) : ℝ)⁻¹) *
        smoothPolynomialWeight F ((a + M * j : ℕ) : ℝ)) *
      (χ ((a + M * j : ℕ) : ZMod q) * conj (ψ ((a + M * j : ℕ) : ZMod r)))‖ ≤
      (3 ^ ((∑ i, (F i).polynomial.derivative.natDegree) + ∑ i, (H i).natDegree) : ℕ) *
        (2 * (a : ℝ)⁻¹ * smoothPolynomialBudget F) * (q * r) := by
  let S := historyWeightRootCuts F H
  have hb := polynomial_weighted_character_progression hqr χ ψ hχ a M N ha hM F S
    (historyWeightRootCuts_factor F H) (polynomialRootCellFlag H S keep)
    (polynomialRootCellFlag_norm H S keep)
  simp_rw [polynomialRootCellFlag_value H S (historyWeightRootCuts_support F H) keep] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by
    have hV := smoothPolynomialBudget_nonneg F
    positivity)
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (3 : ℕ)) (historyWeightRootCuts_card F H)

end Ostmann

end OAI
