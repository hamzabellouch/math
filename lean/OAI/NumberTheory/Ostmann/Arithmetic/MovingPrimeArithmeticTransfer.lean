import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeRowTransfer
import OAI.NumberTheory.Ostmann.Construction.OriginalPivotTransfer

namespace OAI

/-! # The weighted giant-only integer substitution of Section 7.5 -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The inserted giant is `N / (s * U)`. The compensation product `U` is
retained, so the reconstructed integer is the giant and not the whole pivot. -/
noncomputable def movingGiantOffDiagonal {A : Type*} [Fintype A]
    (I : Finset ℕ) (V U : ℕ) (L : A → ℕ) (v : A → ℤ)
    (w : ℕ → ℝ) (c : ℕ → A → ℂ) : ℂ :=
  ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ b,
    if validTransferredPivot I (v a * L b - v b * L a) (s * U) then
      let p := reconstructedPivot (v a * L b - v b * L a) (s * U)
      (w p : ℂ) * c p a * conj (c p b)
    else 0

/-- The exact weighted off-diagonal, with the original coefficient support
and without any multiplicity factor in the integer substitution. -/
theorem movingGiantOffDiagonal_eq {A : Type*} [Fintype A]
    (I : Finset ℕ) (hI : ∀ p ∈ I, 0 < p) (U : ℕ) (hU : 0 < U)
    (B H V : ℕ) (L : A → ℕ) (v : A → ℤ) (w : ℕ → ℝ) (c : ℕ → A → ℂ)
    (hv : ∀ p ∈ I, ∀ a, c p a ≠ 0 → (v a).natAbs ≤ B)
    (hL : ∀ p ∈ I, ∀ a, c p a ≠ 0 → L a ≤ H)
    (hscale : ∀ p ∈ I, 2 * B * H ≤ V * (p * U)) :
    (∑ p ∈ I, (w p : ℂ) * pivotOffDiagonal (p * U) L v (c p)) =
      movingGiantOffDiagonal I V U L v w c := by
  have hUnz : (U : ℤ) ≠ 0 := by exact_mod_cast hU.ne'
  have he (p : ℕ) (s : ℤ) (a b : A) :
      (s ≠ 0 ∧ v a * L b - v b * L a = s * ((p * U : ℕ) : ℤ)) ↔
      (s * (U : ℤ) ≠ 0 ∧ v a * L b - v b * L a = (s * U) * p) := by
    have hmul : s * ((p * U : ℕ) : ℤ) = (s * U) * p := by push_cast; ring
    rw [hmul]
    constructor
    · rintro ⟨hs, hh⟩
      exact ⟨mul_ne_zero hs hUnz, hh⟩
    · rintro ⟨hs, hh⟩
      exact ⟨left_ne_zero_of_mul hs, hh⟩
  calc
    _ = ∑ p ∈ I, ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ b,
        if s * (U : ℤ) ≠ 0 ∧ v a * L b - v b * L a = (s * U) * p
        then (w p : ℂ) * c p a * conj (c p b) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [pivotOffDiagonal_frequency_on_support (p * U) B H V
        (Nat.mul_pos (hI p hp) hU) L v (c p) (hv p hp) (hL p hp) (hscale p hp)]
      simp only [Finset.mul_sum, mul_ite, mul_zero]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [he p s a b, mul_assoc]
    _ = movingGiantOffDiagonal I V U L v w c := by
      unfold movingGiantOffDiagonal
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      exact transferred_pivot_substitution I hI _ (s * U)
        (fun p => (w p : ℂ) * c p a * conj (c p b))

end Ostmann

end OAI
