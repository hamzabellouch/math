import OAI.Analysis.Laughlin.Spin.Basic
import OAI.Analysis.Laughlin.Spin.Sl2Orthogonal

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericHighest_orthogonal (A B z w : ℕ) (hzA : z ≤ A) (hzB : z ≤ B) (hwA : w ≤ A) (hwB : w ≤ B)
    (hzw : z ≠ w) :
    (∑ i, genericHighest A B z hzA hzB i*genericHighest A B w hwA hwB i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_cases he : i.1.val+i.2.val=z
  · have hh : i.1.val+i.2.val ≠ w := by omega
    have hv : genericHighest A B w hwA hwB i = 0 :=
      extendWeightSlice_off A B w hwA hwB _ i hh
    rw [hv,mul_zero]
  · have hv : genericHighest A B z hzA hzB i = 0 :=
      extendWeightSlice_off A B z hzA hzB _ i he
    rw [hv,zero_mul]

theorem genericDescendant_orthogonal (A B z w n m : ℕ) (hzA : z ≤ A) (hzB : z ≤ B) (hwA : w ≤ A) (hwB : w ≤ B)
    (hne : z ≠ w ∨ n ≠ m) :
    (∑ i, genericDescendant A B z hzA hzB n i*genericDescendant A B w hwA hwB m i) = 0 := by
  apply descendants_orthogonal (totalRaise A B) (totalWeight A B)
    ((totalRaise A B)ᵀ) (genericHighest A B z hzA hzB) (genericHighest A B w hwA hwB)
    (genericCoupledWeight A B w) (total_raise_lower_commutator _ _) (total_weight_lower_commutator _ _)
    (Matrix.transpose_transpose _) (genericHighest_weight A B w hwA hwB)
    (genericHighest_raising_zero A B z hzA hzB) (genericHighest_raising_zero A B w hwA hwB) n m
  rcases hne with h | h
  · exact Or.inl (genericHighest_orthogonal A B z w hzA hzB hwA hwB h)
  · exact Or.inr h

theorem genericUnitDescendant_orthogonal (A B z w n m : ℕ) (hzA : z ≤ A) (hzB : z ≤ B) (hwA : w ≤ A) (hwB : w ≤ B)
    (hne : z ≠ w ∨ n ≠ m) :
    (∑ i, genericUnitDescendant A B z hzA hzB n i *
      genericUnitDescendant A B w hwA hwB m i) = 0 := by
  unfold genericUnitDescendant
  simp only [Pi.smul_apply,smul_eq_mul]
  calc
    _ = (Real.sqrt (vectorNormSq (genericDescendant A B z hzA hzB n)))⁻¹ *
      (Real.sqrt (vectorNormSq (genericDescendant A B w hwA hwB m)))⁻¹ *
      (∑ i, genericDescendant A B z hzA hzB n i*genericDescendant A B w hwA hwB m i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi; ring
    _ = 0 := by rw [genericDescendant_orthogonal A B z w n m hzA hzB hwA hwB hne,mul_zero]

end Laughlin.Spin

end OAI
