import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Uniform local projections

The finite quotient argument underlying equation `valuation-tail` in
paper 031-01. A uniformly chosen element of a finite additive group maps
uniformly to its image. A single element of large additive order in that
image bounds the mass of the zero fiber. No independence between different
component projections is used.
-/

namespace DukePrimeDegree

/-- A single element in the image gives a bound for the proportion of
 the zero fiber of an additive homomorphism. -/
theorem kernel_fraction_le_inverse_order
    {A B : Type*} [AddGroup A] [AddGroup B] [Finite A] [Finite B]
    (f : A →+ B) (x : A) :
    (Nat.card f.ker : ℝ) / Nat.card A ≤ 1 / (addOrderOf (f x) : ℝ) := by
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card A := by
    simpa only [AddSubgroup.index_ker] using f.ker.card_mul_index
  have hrange : addOrderOf (f x) ≤ Nat.card f.range := by
    exact Nat.le_of_dvd Nat.card_pos (f.range.addOrderOf_dvd_natCard ⟨x, rfl⟩)
  have hprod : Nat.card f.ker * addOrderOf (f x) ≤ Nat.card A := by
    calc
      Nat.card f.ker * addOrderOf (f x) ≤ Nat.card f.ker * Nat.card f.range :=
        Nat.mul_le_mul_left _ hrange
      _ = Nat.card A := hcard
  have hA : (0 : ℝ) < Nat.card A := by exact_mod_cast (Nat.card_pos (α := A))
  have ho : (0 : ℝ) < addOrderOf (f x) := by exact_mod_cast addOrderOf_pos (f x)
  apply (div_le_div_iff₀ hA ho).mpr
  simpa only [one_mul, Nat.cast_mul] using (show
    (Nat.card f.ker * addOrderOf (f x) : ℝ) ≤ Nat.card A by exact_mod_cast hprod)

/-- The form used for a component modulo the `k`th power of its maximal
 ideal: a unit generates at least `ℓ ^ ceil(k/e)` distinct additive images. -/
theorem kernel_fraction_le_prime_power
    {A B : Type*} [AddGroup A] [AddGroup B] [Finite A] [Finite B]
    (f : A →+ B) (x : A) (ℓ a : ℕ) (hℓ : 0 < ℓ)
    (horder : ℓ ^ a ≤ addOrderOf (f x)) :
    (Nat.card f.ker : ℝ) / Nat.card A ≤ (ℓ : ℝ) ^ (-(a : ℤ)) := by
  calc
    (Nat.card f.ker : ℝ) / Nat.card A ≤ 1 / (addOrderOf (f x) : ℝ) :=
      kernel_fraction_le_inverse_order f x
    _ ≤ 1 / (ℓ : ℝ) ^ a := by
      apply one_div_le_one_div_of_le
      · exact_mod_cast pow_pos hℓ a
      · exact_mod_cast horder
    _ = (ℓ : ℝ) ^ (-(a : ℤ)) := by simp [zpow_neg, one_div]

end DukePrimeDegree

end OAI
