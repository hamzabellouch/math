import OAI.NumberTheory.Ostmann.Characters.PivotSquareSplit

namespace OAI

/-! # Eliminating the extended integer by its exact signed quotient -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- The positive integer retained by a transferred frequency, when its
integrality and range indicators hold. -/
def reconstructedPivot (N s : ℤ) : ℕ := (N / s).toNat

theorem reconstructedPivot_of_eq (N s : ℤ) (hs : s ≠ 0) (M : ℕ)
    (h : N = s * M) : reconstructedPivot N s = M := by
  rw [reconstructedPivot, Int.ediv_eq_of_eq_mul_right hs h, Int.toNat_natCast]

def validTransferredPivot (T : Finset ℕ) (N s : ℤ) : Prop :=
  s ≠ 0 ∧ s ∣ N ∧ 0 < N / s ∧ reconstructedPivot N s ∈ T

theorem validTransferredPivot_of_eq (T : Finset ℕ) (N s : ℤ) (hs : s ≠ 0)
    (M : ℕ) (hM : 0 < M) (hMT : M ∈ T) (h : N = s * M) :
    validTransferredPivot T N s := by
  refine ⟨hs, ?_, ?_, ?_⟩
  · rw [h]
    exact dvd_mul_right s M
  · rw [Int.ediv_eq_of_eq_mul_right hs h]
    exact_mod_cast hM
  · rw [reconstructedPivot_of_eq N s hs M h]
    exact hMT

theorem validTransferredPivot_equation (T : Finset ℕ) (N s : ℤ)
    (h : validTransferredPivot T N s) :
    N = s * reconstructedPivot N s := by
  rw [reconstructedPivot, Int.toNat_of_nonneg h.2.2.1.le]
  exact (Int.mul_ediv_cancel' h.2.1).symm

/-- The sum over positive integers has exactly one retained term. This
identity is valid for arbitrary coefficients, including all inherited weights. -/
theorem transferred_pivot_substitution (T : Finset ℕ)
    (hT : ∀ M ∈ T, 0 < M) (N s : ℤ) (f : ℕ → ℂ) :
    (∑ M ∈ T, if s ≠ 0 ∧ N = s * M then f M else 0) =
      if validTransferredPivot T N s then f (reconstructedPivot N s) else 0 := by
  by_cases h : validTransferredPivot T N s
  · rw [ite_eq_left h, Finset.sum_eq_single (reconstructedPivot N s)]
    · rw [ite_eq_left ⟨h.1, validTransferredPivot_equation T N s h⟩]
    · intro M _ hne
      rw [ite_eq_right]
      rintro ⟨hs, he⟩
      exact hne (reconstructedPivot_of_eq N s hs M he).symm
    · exact fun hn => (hn h.2.2.2).elim
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro M hMT
    rw [ite_eq_right]
    rintro ⟨hs, he⟩
    exact h (validTransferredPivot_of_eq T N s hs M (hT M hMT) hMT he)

/-- Expanded copied branches now carry only their reconstructed pivot,
with all integer range and sign tests retained as indicators. -/
theorem offDiagonal_pivot_substitution {A : Type*} [Fintype A]
    (T : Finset ℕ) (hT : ∀ M ∈ T, 0 < M) (S : Finset ℤ)
    (L : A → ℕ) (v : A → ℤ) (c : ℕ → A → ℂ) :
    (∑ M ∈ T, ∑ s ∈ S, ∑ a, ∑ b,
      if s ≠ 0 ∧ v a * L b - v b * L a = s * M then c M a * conj (c M b) else 0) =
    ∑ s ∈ S, ∑ a, ∑ b,
      if validTransferredPivot T (v a * L b - v b * L a) s
      then c (reconstructedPivot (v a * L b - v b * L a) s) a *
        conj (c (reconstructedPivot (v a * L b - v b * L a) s) b) else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact transferred_pivot_substitution T hT _ s (fun M => c M a * conj (c M b))

/-- The whole extended off-diagonal equals the next arithmetic amplitude.
Only the actual reconstructed integer is retained in each term. -/
theorem sum_pivotOffDiagonal_eq_substitution {A : Type*} [Fintype A]
    (T : Finset ℕ) (hT : ∀ M ∈ T, 0 < M) (B H V : ℕ)
    (L : A → ℕ) (v : A → ℤ) (c : ℕ → A → ℂ)
    (hv : ∀ a, (v a).natAbs ≤ B) (hL : ∀ a, L a ≤ H)
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
      exact pivotOffDiagonal_eq_frequency_sum M B H V (hT M hMT) L v (c M)
        hv hL (hscale M hMT)
    _ = _ := offDiagonal_pivot_substitution T hT (transferFrequencyRange V) L v c

end Ostmann

end OAI
