import OAI.Analysis.Laughlin.Spin.Sl2DescendantNorm
import OAI.Analysis.Laughlin.Spin.TotalSl2Matrix
import OAI.Analysis.Laughlin.ThreeBody.Descendants

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

def coupledWeight (Q z : ℕ) : ℕ := 3*Q-2-2*z

theorem coupledHighest_weight (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    totalWeight (2*Q-2) Q *ᵥ coupledHighest Q z hQ hz =
      (coupledWeight Q z : ℝ) • coupledHighest Q z hQ hz := by
  rw [totalWeight_diagonal]
  funext i
  simp only [Matrix.mulVec,dotProduct,Matrix.diagonal_apply,ite_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  change ((2*Q-2 : ℕ)+ (Q : ℝ)-2*((i.1.val : ℝ)+i.2.val))*coupledHighest Q z hQ hz i =
    (coupledWeight Q z : ℝ)*coupledHighest Q z hQ hz i
  by_cases hi : i.1.val+i.2.val=z
  · have hc : (i.1.val : ℝ)+i.2.val=z := by exact_mod_cast hi
    rw [hc]
    congr 1
    unfold coupledWeight
    rw [Nat.cast_sub (by omega : 2*z ≤ 3*Q-2),Nat.cast_sub (by omega : 2 ≤ 3*Q),
      Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast; ring
  · have he : coupledHighest Q z hQ hz i = 0 :=
      extendWeightSlice_off (2*Q-2) Q z (by omega) hz _ i hi
    rw [he]; ring

theorem coupledHighest_raising_zero (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    totalRaise (2*Q-2) Q *ᵥ coupledHighest Q z hQ hz = 0 := by
  apply extendWeightSlice_highest
  intro p
  exact highestUnit_raising (2*Q-2) Q z p.val (by omega) hz p.isLt

theorem coupledDescendant_norm_pos (Q z n : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hn : n ≤ coupledWeight Q z) : 0 < vectorNormSq (coupledDescendant Q z hQ hz n) := by
  apply descendant_norm_pos (totalRaise (2*Q-2) Q) (totalWeight (2*Q-2) Q)
    ((totalRaise (2*Q-2) Q)ᵀ) (coupledHighest Q z hQ hz) (coupledWeight Q z) n
  · exact total_raise_lower_commutator _ _
  · exact total_weight_lower_commutator _ _
  · exact Matrix.transpose_transpose _
  · exact coupledHighest_weight Q z hQ hz
  · exact coupledHighest_raising_zero Q z hQ hz
  · change 0 < ∑ i, (coupledHighest Q z hQ hz i)^2
    rw [coupledHighest_norm Q z hQ hz]; norm_num
  · exact hn

theorem coupledDescendant_norm_step (Q z n : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    vectorNormSq (coupledDescendant Q z hQ hz (n+1)) =
      (((n : ℝ)+1)*((coupledWeight Q z : ℝ)-n))*vectorNormSq (coupledDescendant Q z hQ hz n) := by
  exact descendant_norm_step (totalRaise (2*Q-2) Q) (totalWeight (2*Q-2) Q)
    ((totalRaise (2*Q-2) Q)ᵀ) (coupledHighest Q z hQ hz) (coupledWeight Q z)
    (total_raise_lower_commutator _ _) (total_weight_lower_commutator _ _)
    (Matrix.transpose_transpose _) (coupledHighest_weight Q z hQ hz)
    (coupledHighest_raising_zero Q z hQ hz) n

noncomputable def normalizedCoupledDescendant (Q z : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) (n : ℕ) :
    PairOrbitalIndex Q → ℝ :=
  (Real.sqrt (vectorNormSq (coupledDescendant Q z hQ hz n)))⁻¹ • coupledDescendant Q z hQ hz n

theorem normalizedCoupledDescendant_norm (Q z n : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q)
    (hn : n ≤ coupledWeight Q z) : vectorNormSq (normalizedCoupledDescendant Q z hQ hz n) = 1 := by
  have hp := coupledDescendant_norm_pos Q z n hQ hz hn
  unfold normalizedCoupledDescendant vectorNormSq
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  change (Real.sqrt (vectorNormSq (coupledDescendant Q z hQ hz n)))⁻¹ ^ 2 *
    vectorNormSq (coupledDescendant Q z hQ hz n) = 1
  rw [inv_pow,Real.sq_sqrt (le_of_lt hp),inv_mul_cancel₀ (ne_of_gt hp)]

theorem normalizedCoupledDescendant_eigen (Q z n : ℕ) (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    (threeGram Q-1) *ᵥ normalizedCoupledDescendant Q z hQ hz n =
      gramEigenvalueFormula Q z • normalizedCoupledDescendant Q z hQ hz n := by
  unfold normalizedCoupledDescendant
  rw [Matrix.mulVec_smul,threeGram_sub_one_descendant_eigen,smul_comm]

end Laughlin.Spin

end OAI
