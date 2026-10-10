import OAI.Analysis.Laughlin.Spin.DescendantNorm
import OAI.Analysis.Laughlin.Spin.Sl2Orthogonal

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem coupledHighest_orthogonal (Q z w : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (hw : w ≤ Q)
    (hzw : z ≠ w) :
    (∑ i, coupledHighest Q z hQ hz i*coupledHighest Q w hQ hw i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_cases he : i.1.val+i.2.val=z
  · have hh : i.1.val+i.2.val ≠ w := by omega
    have hv : coupledHighest Q w hQ hw i = 0 :=
      extendWeightSlice_off (2*Q-2) Q w (by omega) hw _ i hh
    rw [hv,mul_zero]
  · have hv : coupledHighest Q z hQ hz i = 0 :=
      extendWeightSlice_off (2*Q-2) Q z (by omega) hz _ i he
    rw [hv,zero_mul]

theorem coupledDescendant_orthogonal (Q z w n m : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (hw : w ≤ Q)
    (hne : z ≠ w ∨ n ≠ m) :
    (∑ i, coupledDescendant Q z hQ hz n i*coupledDescendant Q w hQ hw m i) = 0 := by
  apply descendants_orthogonal (totalRaise (2*Q-2) Q) (totalWeight (2*Q-2) Q)
    ((totalRaise (2*Q-2) Q)ᵀ) (coupledHighest Q z hQ hz) (coupledHighest Q w hQ hw)
    (coupledWeight Q w) (total_raise_lower_commutator _ _) (total_weight_lower_commutator _ _)
    (Matrix.transpose_transpose _) (coupledHighest_weight Q w hQ hw)
    (coupledHighest_raising_zero Q z hQ hz) (coupledHighest_raising_zero Q w hQ hw) n m
  rcases hne with h | h
  · exact Or.inl (coupledHighest_orthogonal Q z w hQ hz hw h)
  · exact Or.inr h

theorem normalizedCoupledDescendant_orthogonal (Q z w n m : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (hw : w ≤ Q)
    (hne : z ≠ w ∨ n ≠ m) :
    (∑ i, normalizedCoupledDescendant Q z hQ hz n i *
      normalizedCoupledDescendant Q w hQ hw m i) = 0 := by
  unfold normalizedCoupledDescendant
  simp only [Pi.smul_apply,smul_eq_mul]
  calc
    _ = (Real.sqrt (vectorNormSq (coupledDescendant Q z hQ hz n)))⁻¹ *
      (Real.sqrt (vectorNormSq (coupledDescendant Q w hQ hw m)))⁻¹ *
      (∑ i, coupledDescendant Q z hQ hz n i*coupledDescendant Q w hQ hw m i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi; ring
    _ = 0 := by rw [coupledDescendant_orthogonal Q z w n m hQ hz hw hne,mul_zero]

end Laughlin.Spin

end OAI
