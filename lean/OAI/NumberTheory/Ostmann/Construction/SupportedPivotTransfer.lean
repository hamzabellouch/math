import OAI.NumberTheory.Ostmann.Characters.PivotArithmeticTransfer
import OAI.NumberTheory.Ostmann.Construction.TransferredPivotSubstitution

namespace OAI

/-! # Pivot transfer with bounds imposed on the actual nonzero support -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- The residue identity is needed only for pairs with nonzero coefficients.
Thus the original coprimality indicator stays inside the coefficient. -/
theorem pivot_square_split_on_support {A : Type*} [Fintype A]
    (M : ℕ) [NeZero M] (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hL : ∀ a, c a ≠ 0 → (L a).Coprime M) :
    (∑ u : Fin M, ‖groupedCoefficient (fun a => pivotResidueKey M (L a) (v a)) c u‖ ^ 2) =
      (pivotDiagonal L v c).re + (pivotOffDiagonal M L v c).re := by
  have hh := diagonal_real_eq_sum_sq (fun a => pivotResidueKey M (L a) (v a)) c (fun _ => 1)
  simp only [Complex.ofReal_one, one_mul] at hh
  rw [← hh, ← Complex.add_re]
  congr 1
  unfold pivotDiagonal pivotOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : c a = 0
  · simp [ha]
  by_cases hb : c b = 0
  · simp [hb]
  simp only [pivotResidueKey_eq_iff M (L a) (L b) (hL a ha) (hL b hb)]
  by_cases hz : v a * L b - v b * L a = 0
  · simp [hz]
  · by_cases hd : (M : ℤ) ∣ v a * L b - v b * L a <;> simp [hz, hd]

theorem pivotDiagonal_nonneg_on_support {A : Type*} [Fintype A]
    (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hpos : ∀ a, c a ≠ 0 → 0 < L a) (hv : ∀ a, c a ≠ 0 → v a ≠ 0)
    (hlarge : ∀ a, c a ≠ 0 → ∀ q, q.Prime → q ∣ L a → (v a).natAbs < q) :
    0 ≤ (pivotDiagonal L v c).re := by
  have he : pivotDiagonal L v c =
      ∑ a, ∑ b, if (L a, v a) = (L b, v b) then c a * conj (c b) else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases ha : c a = 0
    · simp [ha]
    by_cases hb : c b = 0
    · simp [hb]
    simp only [pivot_zero_numerator_iff (L a) (L b) (hpos a ha) (v a) (v b)
      (hv a ha) (hv b hb) (hlarge a ha) (hlarge b hb), Prod.mk.injEq]
  rw [he]
  convert finite_key_square_nonneg (fun a => (L a, v a)) c using 1
  congr 2
  funext a
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : (L a, v a) = (L b, v b) <;> simp only [h, ite_true, ite_false]

theorem pivotOffDiagonal_frequency_on_support {A : Type*} [Fintype A]
    (M B H V : ℕ) (hM : 0 < M) (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hv : ∀ a, c a ≠ 0 → (v a).natAbs ≤ B)
    (hL : ∀ a, c a ≠ 0 → L a ≤ H) (hscale : 2 * B * H ≤ V * M) :
    pivotOffDiagonal M L v c = ∑ s ∈ transferFrequencyRange V,
      ∑ a, ∑ b, if s ≠ 0 ∧ v a * L b - v b * L a = s * M
        then c a * conj (c b) else 0 := by
  have he (a b : A) :
      (if v a * L b - v b * L a ≠ 0 ∧ (M : ℤ) ∣ v a * L b - v b * L a
        then c a * conj (c b) else 0) =
      ∑ s ∈ transferFrequencyRange V,
        if s ≠ 0 ∧ v a * L b - v b * L a = s * M then c a * conj (c b) else 0 := by
    by_cases ha : c a = 0
    · simp [ha]
    by_cases hb : c b = 0
    · simp [hb]
    exact transferred_frequency_sum_bounded M (L a) (L b) B H V hM (v a) (v b)
      (hv a ha) (hv b hb) (hL a ha) (hL b hb) hscale _
  unfold pivotOffDiagonal
  simp_rw [he]
  calc
    _ = ∑ a, ∑ s ∈ transferFrequencyRange V, ∑ b,
        if s ≠ 0 ∧ v a * L b - v b * L a = s * M then c a * conj (c b) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- Positivity of the active product alone makes the zero-numerator part
a square. Frequency size is needed later to identify its prime matching,
but is not needed for this nonnegativity step. -/
theorem pivotDiagonal_nonneg_of_positive_support {A : Type*} [Fintype A]
    (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hpos : ∀ a, c a ≠ 0 → 0 < L a) : 0 ≤ (pivotDiagonal L v c).re := by
  have hh := finite_key_square_nonneg (fun a => (v a : ℚ) / (L a : ℚ)) c
  convert hh using 1
  congr 2
  unfold pivotDiagonal
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : c a = 0
  · simp [ha]
  by_cases hb : c b = 0
  · simp [hb]
  have hLa : (L a : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos a ha))
  have hLb : (L b : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos b hb))
  have he : v a * L b - v b * L a = 0 ↔
      (v a : ℚ) / (L a : ℚ) = (v b : ℚ) / (L b : ℚ) := by
    rw [div_eq_div_iff hLa hLb]
    constructor
    · intro h
      exact_mod_cast sub_eq_zero.mp h
    · intro h
      exact sub_eq_zero.mpr (by exact_mod_cast h)
  by_cases hz : v a * L b - v b * L a = 0
  · simp only [hz, he.mp hz, ite_true]
  · simp only [hz, mt he.mpr hz, ite_false]

/-- This is the extended integer sum with the original support left in its
coefficients. Every off-diagonal term has one forced positive pivot. -/
theorem sum_pivotOffDiagonal_substitution_on_support {A : Type*} [Fintype A]
    (T : Finset ℕ) (hT : ∀ M ∈ T, 0 < M) (B H V : ℕ)
    (L : A → ℕ) (v : A → ℤ) (c : ℕ → A → ℂ)
    (hv : ∀ M ∈ T, ∀ a, c M a ≠ 0 → (v a).natAbs ≤ B)
    (hL : ∀ M ∈ T, ∀ a, c M a ≠ 0 → L a ≤ H)
    (hscale : ∀ M ∈ T, 2 * B * H ≤ V * M) :
    (∑ M ∈ T, pivotOffDiagonal M L v (c M)) =
      ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ b,
        if validTransferredPivot T (v a * L b - v b * L a) s
        then c (reconstructedPivot (v a * L b - v b * L a) s) a *
          conj (c (reconstructedPivot (v a * L b - v b * L a) s) b) else 0 := by
  calc
    _ = ∑ M ∈ T, ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ b,
        if s ≠ 0 ∧ v a * L b - v b * L a = s * M then c M a * conj (c M b) else 0 := by
      apply Finset.sum_congr rfl
      intro M hMT
      exact pivotOffDiagonal_frequency_on_support M B H V (hT M hMT) L v (c M)
        (hv M hMT) (hL M hMT) (hscale M hMT)
    _ = _ := offDiagonal_pivot_substitution T hT (transferFrequencyRange V) L v c

end Ostmann

end OAI
