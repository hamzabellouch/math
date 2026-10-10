import OAI.Analysis.Laughlin.Spin.Sl2DescendantNorm
import OAI.Analysis.Laughlin.Spin.TotalSl2Matrix

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

def genericCoupledWeight (A B z : ℕ) : ℕ := A+B-2*z

noncomputable def genericHighest (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    SpinIndex A B → ℝ :=
  extendWeightSlice A B z hA hB (fun p => highestUnit A B z p.val)

theorem genericHighest_norm (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    vectorNormSq (genericHighest A B z hA hB) = 1 := by
  unfold vectorNormSq genericHighest
  simp only [pow_two]
  rw [sum_extendWeightSlice]
  simp_rw [extendWeightSlice_at,← pow_two]
  simpa only [← Fin.sum_univ_eq_sum_range] using highestUnit_norm A B z hA hB

theorem genericHighest_weight (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    totalWeight A B *ᵥ genericHighest A B z hA hB =
      (genericCoupledWeight A B z : ℝ) • genericHighest A B z hA hB := by
  rw [totalWeight_diagonal]
  funext i
  simp only [Matrix.mulVec,dotProduct,Matrix.diagonal_apply,ite_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  change ((A : ℝ)+B-2*((i.1.val : ℝ)+i.2.val))*genericHighest A B z hA hB i =
    (genericCoupledWeight A B z : ℝ)*genericHighest A B z hA hB i
  by_cases hi : i.1.val+i.2.val=z
  · have hc : (i.1.val : ℝ)+i.2.val=z := by exact_mod_cast hi
    rw [hc]
    congr 1
    unfold genericCoupledWeight
    rw [Nat.cast_sub (by omega : 2*z ≤ A+B)]
    push_cast; ring
  · have he : genericHighest A B z hA hB i = 0 :=
      extendWeightSlice_off A B z hA hB _ i hi
    rw [he]; ring

theorem genericHighest_raising_zero (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    totalRaise A B *ᵥ genericHighest A B z hA hB = 0 := by
  apply extendWeightSlice_highest
  intro p
  exact highestUnit_raising A B z p.val hA hB p.isLt

noncomputable def genericDescendant (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) (n : ℕ) :
    SpinIndex A B → ℝ :=
  ((totalRaise A B)ᵀ ^ n) *ᵥ genericHighest A B z hA hB

theorem genericDescendant_succ (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) (n : ℕ) :
    genericDescendant A B z hA hB (n+1) =
      (totalRaise A B)ᵀ *ᵥ genericDescendant A B z hA hB n := by
  simp only [genericDescendant,pow_succ',Matrix.mulVec_mulVec]

theorem genericDescendant_norm_pos (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hn : n ≤ genericCoupledWeight A B z) :
    0 < vectorNormSq (genericDescendant A B z hA hB n) := by
  apply descendant_norm_pos (totalRaise A B) (totalWeight A B) ((totalRaise A B)ᵀ)
    (genericHighest A B z hA hB) (genericCoupledWeight A B z) n
  · exact total_raise_lower_commutator _ _
  · exact total_weight_lower_commutator _ _
  · exact Matrix.transpose_transpose _
  · exact genericHighest_weight A B z hA hB
  · exact genericHighest_raising_zero A B z hA hB
  · rw [genericHighest_norm]; norm_num
  · exact hn

theorem genericDescendant_norm_step (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    vectorNormSq (genericDescendant A B z hA hB (n+1)) =
      (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n))*
        vectorNormSq (genericDescendant A B z hA hB n) := by
  exact descendant_norm_step (totalRaise A B) (totalWeight A B) ((totalRaise A B)ᵀ)
    (genericHighest A B z hA hB) (genericCoupledWeight A B z)
    (total_raise_lower_commutator _ _) (total_weight_lower_commutator _ _)
    (Matrix.transpose_transpose _) (genericHighest_weight A B z hA hB)
    (genericHighest_raising_zero A B z hA hB) n

noncomputable def genericUnitDescendant (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) (n : ℕ) :
    SpinIndex A B → ℝ :=
  (Real.sqrt (vectorNormSq (genericDescendant A B z hA hB n)))⁻¹ • genericDescendant A B z hA hB n

theorem genericUnitDescendant_norm (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hn : n ≤ genericCoupledWeight A B z) :
    vectorNormSq (genericUnitDescendant A B z hA hB n) = 1 := by
  have hp := genericDescendant_norm_pos A B z n hA hB hn
  unfold genericUnitDescendant vectorNormSq
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  change (Real.sqrt (vectorNormSq (genericDescendant A B z hA hB n)))⁻¹ ^ 2 *
    vectorNormSq (genericDescendant A B z hA hB n) = 1
  rw [inv_pow,Real.sq_sqrt (le_of_lt hp),inv_mul_cancel₀ (ne_of_gt hp)]

theorem genericUnitDescendant_zero (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    genericUnitDescendant A B z hA hB 0 = genericHighest A B z hA hB := by
  simp [genericUnitDescendant,genericDescendant,genericHighest_norm]

end Laughlin.Spin

end OAI
