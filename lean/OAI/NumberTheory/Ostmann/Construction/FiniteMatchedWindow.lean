import OAI.NumberTheory.Ostmann.Construction.FiniteMatchedPrior

namespace OAI

/-! # Counterpart normalization on the original H and Y product law -/

namespace Ostmann
open scoped BigOperators Classical

theorem finite_prime_prior_product_lower {H Y : Type*} [Fintype H] [Fintype Y]
    (P : Finset ℕ) (Q : H ⊕ Y → Finset ℕ) (lo : H → ℝ)
    (hcell : ∀ h p, p ∈ Q (.inl h) → lo h ≤ (p : ℝ))
    (hlo : ∀ h, 0 ≤ lo h) (x : H ⊕ Y → P)
    (hx : (∏ i, primeSubsetPrior P (Q i) (x i)) ≠ 0) :
    (∏ h, lo h) ≤ ∏ h, (x (.inl h) : ℝ) := by
  apply Finset.prod_le_prod₀ (fun h _ => hlo h)
  intro h _
  exact hcell h _ (primeSubsetPrior_support P _ _
    ((Finset.prod_ne_zero_iff.mp hx) (.inl h) (Finset.mem_univ _)))

/-- The normalizing factor is pulled outside all H/Y summation. The inserted
cutoff follows from the original cell endpoints whenever the prior is nonzero. -/
theorem finite_matched_window_eq {H Y : Type*} [Fintype H] [Fintype Y]
    (P : Finset ℕ) (Q : H ⊕ Y → Finset ℕ) (e : Equiv.Perm H)
    (F : (H ⊕ Y → P) → ℂ) (lo : H → ℝ) (hlo : ∀ h, 0 ≤ lo h)
    (hcell : ∀ h p, p ∈ Q (.inl h) → lo h ≤ (p : ℝ))
    (Z : ℝ) (hZ : 0 < Z) (hscale : Z ≤ ∏ h, lo h) :
    (∑ x : H ⊕ Y → P,
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) * F x) =
    (((∏ h, (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ : ℝ) : ℂ) *
      ∑ x : H ⊕ Y → P, ((Z / (∏ h, (x (.inl h) : ℝ)) : ℝ) : ℂ) *
        (if Z ≤ ∏ h, (x (.inl h) : ℝ) then
          ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
          (((∏ h, if (x (.inl h) : ℕ) ∈ Q (.inl (e.symm h)) then (1 : ℝ) else 0) : ℂ) * F x)
        else 0) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : (∏ i, primeSubsetPrior P (Q i) (x i)) = 0
  · simp only [hx, Complex.ofReal_zero, zero_mul]
    split_ifs <;> simp only [mul_zero]
  · have hs := hscale.trans (finite_prime_prior_product_lower P Q lo hcell hlo x hx)
    rw [ite_eq_left hs, finite_matched_harmonic_prior P (fun h => Q (.inl h)) e
      (fun h => x (.inl h))]
    have he (C D U : ℝ) : C * D⁻¹ * U = (C * Z⁻¹) * (Z / D) * U := by
      rw [div_eq_mul_inv]
      field_simp
    rw [he]
    push_cast
    simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero]
    ring

noncomputable def retainedHWord (H Y : Type*) [Fintype H] : List (H ⊕ Y) :=
  Finset.univ.toList.map Sum.inl

theorem retainedHWord_length (H Y : Type*) [Fintype H] :
    (retainedHWord H Y).length = Fintype.card H := by
  simp only [retainedHWord, List.length_map, Finset.length_toList, Finset.card_univ]

theorem retainedHWord_prod {H Y : Type*} [Fintype H] (x : H ⊕ Y → ℕ) :
    ((retainedHWord H Y).map x).prod = ∏ h, x (.inl h) := by
  simp only [retainedHWord, List.map_map, Finset.prod_map_toList, Function.comp_apply]

theorem finite_matched_window_bound {H Y : Type*} [Fintype H] [Fintype Y]
    (P : Finset ℕ) (Q : H ⊕ Y → Finset ℕ) (e : Equiv.Perm H)
    (F : (H ⊕ Y → P) → ℂ) (lo : H → ℝ) (hlo : ∀ h, 0 ≤ lo h)
    (hcell : ∀ h p, p ∈ Q (.inl h) → lo h ≤ (p : ℝ))
    (Z : ℝ) (hZ : 0 < Z) (hscale : Z ≤ ∏ h, lo h) (δ : ℝ)
    (hbound : ‖∑ x : H ⊕ Y → P, ((Z / (∏ h, (x (.inl h) : ℝ)) : ℝ) : ℂ) *
        (if Z ≤ ∏ h, (x (.inl h) : ℝ) then
          ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
          (((∏ h, if (x (.inl h) : ℕ) ∈ Q (.inl (e.symm h)) then (1 : ℝ) else 0) : ℂ) * F x)
        else 0)‖ ≤ δ) :
    ‖∑ x : H ⊕ Y → P,
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) * F x‖ ≤
        (∏ h, (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ * δ := by
  rw [finite_matched_window_eq P Q e F lo hlo hcell Z hZ hscale, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end Ostmann

end OAI
