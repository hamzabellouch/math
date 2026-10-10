import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Multiplying support bounds under the original independent prior

The test at a split can depend on the entire already exposed prefix. This
records the order of exposure, so future validity never changes its law.
-/

namespace Ostmann

open scoped BigOperators Classical

@[implicit_reducible] def SplitSamples (A : Type) : ℕ → Type _
  | 0 => Unit
  | n + 1 => A × SplitSamples A n

instance splitSamplesFintype (A : Type) [Fintype A] (n : ℕ) : Fintype (SplitSamples A n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact @instFintypeProd _ _ _ ih

noncomputable def sequentialSupport {A : Type} (test : List A → A → Prop)
    (past : List A) : (n : ℕ) → SplitSamples A n → ℝ
  | 0, _ => 1
  | n + 1, x => if test past x.1 then sequentialSupport test (x.1 :: past) n x.2 else 0

theorem sequentialSupport_nonneg {A : Type} (test : List A → A → Prop)
    (past : List A) (n : ℕ) (x : SplitSamples A n) :
    0 ≤ sequentialSupport test past n x := by
  induction n generalizing past with
  | zero => exact zero_le_one
  | succ n ih =>
    change 0 ≤ if test past x.1 then sequentialSupport test (x.1 :: past) n x.2 else 0
    split_ifs
    · exact ih _ _
    · exact le_rfl

/-- Prefix-adapted tests multiply their bounds without conditioning on
the complete support event. -/
theorem sequentialSupport_average_le {A : Type} [Fintype A] [Nonempty A]
    (test : List A → A → Prop) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (htest : ∀ past, (Fintype.card A : ℝ)⁻¹ *
      (∑ x : A, if test past x then (1 : ℝ) else 0) ≤ ρ)
    (past : List A) (n : ℕ) :
    (Fintype.card A : ℝ)⁻¹ ^ n *
        (∑ x : SplitSamples A n, sequentialSupport test past n x) ≤ ρ ^ n := by
  induction n generalizing past with
  | zero => simp [sequentialSupport, SplitSamples]
  | succ n ih =>
    change (Fintype.card A : ℝ)⁻¹ ^ (n + 1) *
      (∑ x : A × SplitSamples A n,
        if test past x.1 then sequentialSupport test (x.1 :: past) n x.2 else 0) ≤ _
    rw [Fintype.sum_prod_type, pow_succ]
    have heq : (∑ a : A, ∑ x : SplitSamples A n,
        if test past a then sequentialSupport test (a :: past) n x else 0) =
        ∑ a : A, (if test past a then (1 : ℝ) else 0) *
          (∑ x : SplitSamples A n, sequentialSupport test (a :: past) n x) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : test past a <;> simp [ha]
    rw [heq]
    calc
      _ = (Fintype.card A : ℝ)⁻¹ *
          ∑ a : A, (if test past a then (1 : ℝ) else 0) *
            ((Fintype.card A : ℝ)⁻¹ ^ n *
              (∑ x : SplitSamples A n, sequentialSupport test (a :: past) n x)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ ≤ (Fintype.card A : ℝ)⁻¹ *
          ∑ a : A, (if test past a then (1 : ℝ) else 0) * ρ ^ n := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
        exact Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (ih (a :: past)) (by split_ifs <;> norm_num)
      _ = ((Fintype.card A : ℝ)⁻¹ *
          ∑ a : A, if test past a then (1 : ℝ) else 0) * ρ ^ n := by
        rw [← Finset.sum_mul, mul_assoc]
      _ ≤ ρ * ρ ^ n := mul_le_mul_of_nonneg_right (htest past) (pow_nonneg hρ n)
      _ = ρ ^ (n + 1) := (pow_succ' ρ n).symm

end Ostmann

end OAI
