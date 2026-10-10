import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticProductSupport

namespace OAI

/-! # Retaining a bounded integrand in the arithmetic support sum -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def arithmeticLeafSupport {Q : ℕ} [NeZero Q]
    (n : ℕ) (data : (ZMod Q)ˣ → List (ZMod Q)ˣ →
      Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (x : TreeLeafTuple (ZMod Q)ˣ n) : ℝ :=
  sequentialSupport
    (fun past y => arithmeticPairSplitTest (data (treeLeafProduct n x) past) y) []
    (2 ^ n - 1) (treeLeafSplitEquiv n (treeLeafProduct n x) ⟨x, rfl⟩)

theorem arithmeticLeafSupport_nonneg {Q : ℕ} [NeZero Q]
    (n : ℕ) (data : (ZMod Q)ˣ → List (ZMod Q)ˣ →
      Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (x : TreeLeafTuple (ZMod Q)ˣ n) : 0 ≤ arithmeticLeafSupport n data x :=
  sequentialSupport_nonneg _ _ _ _

noncomputable def arithmeticWeightedSupportSum {Q : ℕ} [NeZero Q]
    (S : Finset ℤ) (V n : ℕ)
    (data : FrequencyTree (S × S) n → (ZMod Q)ˣ → List (ZMod Q)ˣ →
      Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (F : FrequencyTree (S × S) n → TreeLeafTuple (ZMod Q)ˣ n → ℝ) : ℝ :=
  ∑ t : FrequencyTree (S × S) n,
    frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
      ((Fintype.card (TreeLeafTuple (ZMod Q)ˣ n) : ℝ)⁻¹ *
        ∑ x : TreeLeafTuple (ZMod Q)ˣ n, arithmeticLeafSupport n (data t) x * F t x)

theorem arithmeticWeightedSupportSum_le {Q : ℕ} [NeZero Q]
    (S : Finset ℤ) (V n : ℕ)
    (data : FrequencyTree (S × S) n → (ZMod Q)ˣ → List (ZMod Q)ˣ →
      Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (F : FrequencyTree (S × S) n → TreeLeafTuple (ZMod Q)ˣ n → ℝ)
    (B : ℝ) (hF : ∀ t x, F t x ≤ B) :
    arithmeticWeightedSupportSum S V n data F ≤ B * arithmeticProductSupportSum S V n data := by
  unfold arithmeticWeightedSupportSum
  calc
    _ ≤ ∑ t : FrequencyTree (S × S) n,
        frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
          ((Fintype.card (TreeLeafTuple (ZMod Q)ˣ n) : ℝ)⁻¹ *
            ∑ x : TreeLeafTuple (ZMod Q)ˣ n, arithmeticLeafSupport n (data t) x * B) := by
      apply Finset.sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left _ (frequencyLeafWeight_nonneg _
        (fun _ => by unfold pairedFrequencyLeaf; split_ifs <;> norm_num) n t)
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hF t x)
        (arithmeticLeafSupport_nonneg n (data t) x)
    _ = _ := by
      unfold arithmeticProductSupportSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.sum_mul]
      unfold arithmeticLeafSupport
      ring

end Ostmann

end OAI
