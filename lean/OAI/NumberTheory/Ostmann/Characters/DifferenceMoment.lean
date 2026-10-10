import OAI.NumberTheory.Ostmann.Characters.AffineAction

namespace OAI

/-!
# Means of nonnegative difference convolutions

Removing the zero difference can only decrease the sum. This supplies
the mean bounds for the nonnegative quartet majorants in Section 6.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def differenceMoment {p : ℕ} [NeZero p]
    (f g : ZMod p → ℝ) (y : ZMod p) : ℝ := ∑ x : ZMod p, f x * g (x - y)

theorem differenceMoment_nonneg {p : ℕ} [NeZero p]
    (f g : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (y : ZMod p) :
    0 ≤ differenceMoment f g y :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (hf _) (hg _))

theorem sum_differenceMoment {p : ℕ} [NeZero p] (f g : ZMod p → ℝ) :
    (∑ y : ZMod p, differenceMoment f g y) =
      (∑ x : ZMod p, f x) * ∑ z : ZMod p, g z := by
  have hshift (x : ZMod p) : (∑ y : ZMod p, g (x - y)) = ∑ z : ZMod p, g z := by
    simpa [sub_eq_add_neg] using
      ((Equiv.neg (ZMod p)).trans (Equiv.addLeft x)).bijective.sum_comp g
  unfold differenceMoment
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hshift]
  rw [Finset.sum_mul]

theorem sum_units_differenceMoment_le {p : ℕ} [Fact p.Prime]
    (f g : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    (∑ y : (ZMod p)ˣ, differenceMoment f g y) ≤
      (∑ x : ZMod p, f x) * ∑ z : ZMod p, g z := by
  classical
  rw [← sum_differenceMoment]
  exact Finset.sum_le_sum_of_injOn (fun y : (ZMod p)ˣ => (y : ZMod p))
    Units.val_injective.injOn (Finset.subset_univ _) (fun _ _ => le_rfl)
    (fun y _ _ => differenceMoment_nonneg f g hf hg y)

theorem mean_units_differenceMoment_le {p : ℕ} [Fact p.Prime]
    (f g : ZMod p → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    ((∑ y : (ZMod p)ˣ, differenceMoment f g y) / ((p : ℝ) - 1)) / ((p : ℝ) - 1) ≤
      ((∑ x : ZMod p, f x) / ((p : ℝ) - 1)) *
        ((∑ z : ZMod p, g z) / ((p : ℝ) - 1)) := by
  have hden : 0 ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    linarith
  have h := div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right (sum_units_differenceMoment_le f g hf hg) hden) hden
  convert h using 1
  ring

end Ostmann

end OAI
