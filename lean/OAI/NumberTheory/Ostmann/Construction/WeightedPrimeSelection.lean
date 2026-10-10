import OAI.NumberTheory.Ostmann.Construction.OppositeBiasTransfer

namespace OAI

/-! # Finite weighted deletion estimates for selecting the biased prime block -/

namespace Ostmann

open scoped BigOperators Classical

theorem weighted_square_exception_bound (P : Finset ℕ) (w e : ℕ → ℝ) (δ : ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (hδ : 0 ≤ δ) :
    δ ^ 2 * (∑ p ∈ P.filter (fun p => δ < |e p|), w p) ≤ ∑ p ∈ P, w p * e p ^ 2 := by
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ P.filter (fun p => δ < |e p|), w p * e p ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpP, he⟩ := Finset.mem_filter.mp hp
      have hs : δ ^ 2 ≤ e p ^ 2 := by nlinarith [sq_abs (e p)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hs (hw p hpP)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p hp _ => mul_nonneg (hw p hp) (sq_nonneg _))

theorem weighted_good_mass (P : Finset ℕ) (w : ℕ → ℝ) (good : ℕ → Prop)
    [DecidablePred good] (M E : ℝ)
    (htotal : M ≤ ∑ p ∈ P, w p)
    (hbad : (∑ p ∈ P.filter (fun p => ¬good p), w p) ≤ E) :
    M - E ≤ ∑ p ∈ P.filter good, w p := by
  have hsum := Finset.sum_filter_add_sum_filter_not P good w
  linarith

theorem weighted_bias_superlevel (P : Finset ℕ) (w b : ℕ → ℝ) (δ : ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (hδ : 0 ≤ δ) (hb : ∀ p ∈ P, b p ≤ 1)
    (hbias : δ * (∑ p ∈ P, w p) ≤ ∑ p ∈ P, w p * b p) :
    (δ / 2) * (∑ p ∈ P, w p) ≤ ∑ p ∈ P.filter (fun p => δ / 2 ≤ b p), w p := by
  have hpoint (p : ℕ) (hp : p ∈ P) :
      w p * b p ≤ (δ / 2) * w p + if δ / 2 ≤ b p then w p else 0 := by
    split_ifs with h
    · have hh := mul_le_mul_of_nonneg_left (hb p hp) (hw p hp)
      nlinarith [mul_nonneg hδ (hw p hp)]
    · have hh := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) (hw p hp)
      nlinarith
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter] at hsum
  nlinarith

end Ostmann

end OAI
