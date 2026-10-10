import OAI.NumberTheory.Ostmann.Characters.PivotSquareSplit

namespace OAI

/-! # The actual diagonal/off-diagonal bound from the harmonic pivot prior -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- Coefficients include their positive-integer support, so the impossible
zero-modulus case has an empty coefficient family. -/
noncomputable def positivePivotKey {A : ℕ → Type*}
    (hpos : ∀ M, A M → 0 < M) (L : ∀ M, A M → ℕ) (v : ∀ M, A M → ℤ)
    (M : ℕ) (a : A M) : Fin M := by
  letI : NeZero M := ⟨Nat.ne_of_gt (hpos M a)⟩
  exact pivotResidueKey M (L M a) (v M a)

theorem positivePivotKey_eq_iff {A : ℕ → Type*}
    (hpos : ∀ M, A M → 0 < M) (L : ∀ M, A M → ℕ) (v : ∀ M, A M → ℤ)
    (M : ℕ) (a b : A M) (hL : (L M a).Coprime M) (hR : (L M b).Coprime M) :
    positivePivotKey hpos L v M a = positivePivotKey hpos L v M b ↔
      (M : ℤ) ∣ v M a * L M b - v M b * L M a := by
  let : NeZero M := ⟨Nat.ne_of_gt (hpos M a)⟩
  exact pivotResidueKey_eq_iff M (L M a) (L M b) hL hR (v M a) (v M b)

theorem pivot_square_split_of_key {A : Type*} [Fintype A]
    (M : ℕ) (key : A → Fin M) (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hkey : ∀ a b, key a = key b ↔ (M : ℤ) ∣ v a * L b - v b * L a) :
    (∑ u, ‖groupedCoefficient key c u‖ ^ 2) =
      (pivotDiagonal L v c).re + (pivotOffDiagonal M L v c).re := by
  have he : (∑ u, ‖groupedCoefficient key c u‖ ^ 2) =
      (∑ a, ∑ b, if (M : ℤ) ∣ v a * L b - v b * L a then c a * conj (c b) else 0).re := by
    have hh := diagonal_real_eq_sum_sq key c (fun _ => 1)
    simp only [Complex.ofReal_one, one_mul] at hh
    rw [← hh]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [hkey a b, Complex.star_def]
  rw [he, ← Complex.add_re]
  congr 1
  unfold pivotDiagonal pivotOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hz : v a * L b - v b * L a = 0
  · simp only [hz, ne_eq, not_true_eq_false, false_and, ite_false, add_zero,
      dvd_zero, ite_true]
  · by_cases hd : (M : ℤ) ∣ v a * L b - v b * L a <;> simp [hz, hd]

/-- Both Cauchy steps and the prime-to-integer extension are already included.
The off-diagonal here is the exact complex expanded sum, not a majorant. -/
theorem pivot_arithmetic_transfer_real {A : ℕ → Type*} [∀ M, Fintype (A M)]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (Q : Fin n → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (S : Finset (Fin n → P)) (hS : ∀ x ∈ S, Function.Injective x)
    (T : Finset ℕ) (hT : ∀ x ∈ S, (∏ i, (x i : ℕ)) ∈ T)
    (row : ∀ x : Fin n → P, Fin (∏ i, (x i : ℕ)) → ℂ)
    (hrow : ∀ x ∈ S, ∀ u, ‖row x u‖ ≤ 1)
    (hpos : ∀ M, A M → 0 < M) (L : ∀ M, A M → ℕ) (v : ∀ M, A M → ℤ)
    (hL : ∀ M, ∀ a : A M, (L M a).Coprime M) (c : ∀ M, A M → ℂ) :
    ‖∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
      ∑ a, row x (positivePivotKey hpos L v (∏ i, (x i : ℕ)) a) *
        c (∏ i, (x i : ℕ)) a‖ ^ 2 ≤
    ((n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) *
      ((∑ M ∈ T, (pivotDiagonal (L M) (v M) (c M)).re) +
        (∑ M ∈ T, pivotOffDiagonal M (L M) (v M) (c M)).re) := by
  have ht := pivot_grouped_integer_transfer P hP Q hQP hQ S hS T hT row hrow
    (positivePivotKey hpos L v) c
  have he (M : ℕ) : (∑ u, ‖groupedCoefficient (positivePivotKey hpos L v M) (c M) u‖ ^ 2) =
      (pivotDiagonal (L M) (v M) (c M)).re + (pivotOffDiagonal M (L M) (v M) (c M)).re :=
    pivot_square_split_of_key M _ _ _ _
      (fun a b => positivePivotKey_eq_iff hpos L v M a b (hL M a) (hL M b))
  simp_rw [he] at ht
  rw [Finset.sum_add_distrib] at ht
  simpa only [Complex.re_sum] using ht

/-- Both Cauchy steps and the prime-to-integer extension are already included.
The off-diagonal here is the exact complex expanded sum, not a majorant. -/
theorem pivot_arithmetic_transfer {A : ℕ → Type*} [∀ M, Fintype (A M)]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (Q : Fin n → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (S : Finset (Fin n → P)) (hS : ∀ x ∈ S, Function.Injective x)
    (T : Finset ℕ) (hT : ∀ x ∈ S, (∏ i, (x i : ℕ)) ∈ T)
    (row : ∀ x : Fin n → P, Fin (∏ i, (x i : ℕ)) → ℂ)
    (hrow : ∀ x ∈ S, ∀ u, ‖row x u‖ ≤ 1)
    (hpos : ∀ M, A M → 0 < M) (L : ∀ M, A M → ℕ) (v : ∀ M, A M → ℤ)
    (hL : ∀ M, ∀ a : A M, (L M a).Coprime M) (c : ∀ M, A M → ℂ) :
    ‖∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
      ∑ a, row x (positivePivotKey hpos L v (∏ i, (x i : ℕ)) a) *
        c (∏ i, (x i : ℕ)) a‖ ^ 2 ≤
    ((n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) *
      ((∑ M ∈ T, (pivotDiagonal (L M) (v M) (c M)).re) +
        ‖∑ M ∈ T, pivotOffDiagonal M (L M) (v M) (c M)‖) := by
  have ht := pivot_arithmetic_transfer_real P hP Q hQP hQ S hS T hT row hrow hpos L v hL c
  apply ht.trans
  apply mul_le_mul_of_nonneg_left
  · apply add_le_add le_rfl
    simpa only [Complex.re_sum] using
      (Complex.re_le_norm (∑ M ∈ T, pivotOffDiagonal M (L M) (v M) (c M)))
  · exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun i _ =>
      inv_nonneg.mpr (Finset.sum_nonneg fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p)))

end Ostmann

end OAI
