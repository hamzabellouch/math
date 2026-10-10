import OAI.NumberTheory.Ostmann.Arithmetic.SequentialSupport

namespace OAI

/-! # Distinct frequency bounds at successive exposed splits -/

namespace Ostmann

open scoped BigOperators Classical

theorem sequentialSupport_average_le_product {A : Type} [Fintype A] [Nonempty A]
    (test : List A → A → Prop) (ρ : ℕ → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (htest : ∀ past, (Fintype.card A : ℝ)⁻¹ *
      (∑ x : A, if test past x then (1 : ℝ) else 0) ≤ ρ past.length)
    (past : List A) (n : ℕ) :
    (Fintype.card A : ℝ)⁻¹ ^ n *
        (∑ x : SplitSamples A n, sequentialSupport test past n x) ≤
      ∏ i ∈ Finset.range n, ρ (past.length + i) := by
  induction n generalizing past with
  | zero => simp [sequentialSupport, SplitSamples]
  | succ n ih =>
    let B := ∏ i ∈ Finset.range n, ρ (past.length + 1 + i)
    have hB : 0 ≤ B := Finset.prod_nonneg fun i _ => hρ _
    have htail (a : A) : (Fintype.card A : ℝ)⁻¹ ^ n *
        (∑ x : SplitSamples A n, sequentialSupport test (a :: past) n x) ≤ B := by
      simpa only [List.length_cons, B] using ih (a :: past)
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
          ∑ a : A, (if test past a then (1 : ℝ) else 0) * B := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
        exact Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (htail a) (by split_ifs <;> norm_num)
      _ = ((Fintype.card A : ℝ)⁻¹ *
          ∑ a : A, if test past a then (1 : ℝ) else 0) * B := by
        rw [← Finset.sum_mul, mul_assoc]
      _ ≤ ρ past.length * B := mul_le_mul_of_nonneg_right (htest past) hB
      _ = _ := by
        rw [Finset.prod_range_succ']
        simp only [Nat.add_zero]
        rw [mul_comm (ρ past.length)]
        dsimp [B]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        congr 1
        omega

end Ostmann

end OAI
