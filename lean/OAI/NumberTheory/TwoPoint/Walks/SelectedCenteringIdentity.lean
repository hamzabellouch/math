import OAI.NumberTheory.TwoPoint.Walks.SelectedBinEligibility
import OAI.NumberTheory.TwoPoint.Walks.SelectedRawComparison

namespace OAI

/-! The selected raw sum is exactly the full-divisibility component of the
same centered graph bins. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma selectedRawMean_eq_full_bins {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (R : Finset ℕ) (hR : ∀ q ∈ R, 0 < q)
    (A : Finset (ℕ × ℕ)) (hA : A ⊆ primeTupleDivisors P ×ˢ R)
    (bins : Finset ℤ) (b : ℕ × ℕ → ℤ) (hb : ∀ dq ∈ A, b dq ∈ bins)
    (f g : ℕ → ℂ) (h : ℕ) (T : ℤ → ℝ) :
    selectedRawMean A (fun dq => T (b dq)) f g h =
      ∑ j ∈ bins, fullComplexBin P R
        (fun d q => (d, q) ∈ A ∧ b (d, q) = j) f g h (T j) := by
  rw [selected_fullComplexBin_sum P hprime hdisjoint R hR A hA bins b hb]
  unfold selectedRawMean
  apply sum_congr rfl
  intro dq _
  simp only [Nat.mul_comm dq.1 dq.2]

lemma selected_uncut_sub_raw {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (R : Finset ℕ) (hR : ∀ q ∈ R, 0 < q)
    (A : Finset (ℕ × ℕ)) (hA : A ⊆ primeTupleDivisors P ×ˢ R)
    (bins : Finset ℤ) (b : ℕ × ℕ → ℤ) (hb : ∀ dq ∈ A, b dq ∈ bins)
    (f g : ℕ → ℂ) (h : ℕ) (T : ℤ → ℝ) :
    (∑ j ∈ bins, ((⌊T j⌋₊ : ℂ) / (T j : ℂ)) *
      untwistedUncutPrefix P R (fun d q => (d, q) ∈ A ∧ b (d, q) = j) h
        (fun _ _ _ => True) (fun n => f n.toNat) (fun n => g n.toNat) ⌊T j⌋₊) -
      selectedRawMean A (fun dq => T (b dq)) f g h =
        ∑ j ∈ bins, nonrawComplexBin P R
          (fun d q => (d, q) ∈ A ∧ b (d, q) = j) f g h (T j) := by
  rw [selectedRawMean_eq_full_bins P hprime hdisjoint R hR A hA bins b hb,
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  exact weighted_complex_uncut_sub_full P hprime hdisjoint R _ f g h (T j)

end TwoPointCorrelations

end OAI
